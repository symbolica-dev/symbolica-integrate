use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1463(rules);
    push_rules_rule_1464(rules);
    push_rules_rule_1465(rules);
    push_rules_rule_1466(rules);
    push_rules_rule_1467(rules);
    push_rules_rule_1468(rules);
    push_rules_rule_1469(rules);
    push_rules_rule_1470(rules);
    push_rules_rule_1471(rules);
    push_rules_rule_1472(rules);
    push_rules_rule_1473(rules);
    push_rules_rule_1474(rules);
    push_rules_rule_1475(rules);
    push_rules_rule_1476(rules);
    push_rules_rule_1477(rules);
    push_rules_rule_1478(rules);
    push_rules_rule_1479(rules);
    push_rules_rule_1480(rules);
    push_rules_rule_1481(rules);
    push_rules_rule_1482(rules);
    push_rules_rule_1483(rules);
    push_rules_rule_1484(rules);
    push_rules_rule_1485(rules);
    push_rules_rule_1486(rules);
    push_rules_rule_1487(rules);
    push_rules_rule_1488(rules);
    push_rules_rule_1489(rules);
    push_rules_rule_1490(rules);
    push_rules_rule_1491(rules);
    push_rules_rule_1492(rules);
    push_rules_rule_1493(rules);
    push_rules_rule_1494(rules);
    push_rules_rule_1495(rules);
    push_rules_rule_1496(rules);
    push_rules_rule_1497(rules);
    push_rules_rule_1498(rules);
    push_rules_rule_1499(rules);
    push_rules_rule_1500(rules);
    push_rules_rule_1501(rules);
    push_rules_rule_1502(rules);
    push_rules_rule_1503(rules);
    push_rules_rule_1504(rules);
    push_rules_rule_1505(rules);
    push_rules_rule_1506(rules);
    push_rules_rule_1507(rules);
    push_rules_rule_1508(rules);
    push_rules_rule_1509(rules);
    push_rules_rule_1510(rules);
    push_rules_rule_1511(rules);
    push_rules_rule_1512(rules);
    push_rules_rule_1389(rules);
    push_rules_rule_1390(rules);
    push_rules_rule_1391(rules);
    push_rules_rule_1392(rules);
    push_rules_rule_1393(rules);
    push_rules_rule_1394(rules);
    push_rules_rule_1513(rules);
    push_rules_rule_1514(rules);
    push_rules_rule_1515(rules);
    push_rules_rule_1516(rules);
    push_rules_rule_1517(rules);
    push_rules_rule_1518(rules);
    push_rules_rule_1519(rules);
    push_rules_rule_1520(rules);
    push_rules_rule_1521(rules);
    push_rules_rule_1522(rules);
    push_rules_rule_1523(rules);
    push_rules_rule_1524(rules);
    push_rules_rule_1525(rules);
    push_rules_rule_1526(rules);
    push_rules_rule_1527(rules);
    push_rules_rule_1528(rules);
    push_rules_rule_1529(rules);
    push_rules_rule_1530(rules);
    push_rules_rule_1531(rules);
    push_rules_rule_1532(rules);
    push_rules_rule_1533(rules);
    push_rules_rule_1534(rules);
    push_rules_rule_1535(rules);
    push_rules_rule_1536(rules);
    push_rules_rule_1537(rules);
    push_rules_rule_1538(rules);
    push_rules_rule_1539(rules);
    push_rules_rule_1540(rules);
    push_rules_rule_1541(rules);
    push_rules_rule_1542(rules);
    push_rules_rule_1543(rules);
    push_rules_rule_1544(rules);
    push_rules_rule_1545(rules);
    push_rules_rule_1546(rules);
    push_rules_rule_1547(rules);
    push_rules_rule_1548(rules);
    push_rules_rule_1549(rules);
    push_rules_rule_1550(rules);
    push_rules_rule_1551(rules);
    push_rules_rule_1552(rules);
    push_rules_rule_1553(rules);
    push_rules_rule_1554(rules);
    push_rules_rule_1555(rules);
    push_rules_rule_1556(rules);
    push_rules_rule_1557(rules);
    push_rules_rule_1558(rules);
    push_rules_rule_1559(rules);
    push_rules_rule_1560(rules);
    push_rules_rule_1561(rules);
    push_rules_rule_1562(rules);
    push_rules_rule_1563(rules);
    push_rules_rule_1564(rules);
    push_rules_rule_1565(rules);
    push_rules_rule_1566(rules);
    push_rules_rule_1567(rules);
    push_rules_rule_1568(rules);
    push_rules_rule_1569(rules);
    push_rules_rule_1570(rules);
    push_rules_rule_1571(rules);
}

fn push_rules_rule_1463(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1463,
        source: "Int[(d_+e_.*x_^2)/(b_.*x_^2+c_.*x_^4)^(3/4),x_Symbol] :=
          -2*(c*d-b*e)*(b*x^2+c*x^4)^(1/4)/(b*c*x) + e/c \\[Star] Int[(b*x^2+c*x^4)^(1/4)/x^2,x] /;
        FreeQ[{b,c,d,e},x]",
        desc: "Trinomial recurrence 2a with a=0, m=0 and n (2 p+1)+1\\[Equal]0 composed with trinomial recurrene 5 with a=0",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)) / (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(Atom::num(3) / Atom::num(4)),
        with: [b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__],
        when: { freeq!([b__, c__, d__, e__], x_) },
        rhs: {
            let quartic = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_simp(&(-Atom::num(2)
                    * (&c__ * &d__ - &b__ * &e__)
                    * quartic.pow(Atom::num(1) / Atom::num(4))
                    / (&b__ * &c__ * x_)), x_)
                    + rubi_star(&e__ / &c__, rubi_rhs_int(
                            &(quartic.pow(Atom::num(1) / Atom::num(4)) / x_.pow(2)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_1464(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1464,
        source: "Int[(d_+e_.*x_^2)*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          e*(b*x^2+c*x^4)^(p+1)/(c*(4*p+3)*x) /;
        FreeQ[{b,c,d,e,p},x] && Not[IntegerQ[p]] && NeQ[4*p+3,0] && EqQ[b*e*(2*p+1)-c*d*(4*p+3),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__, p_],
        when: {
            freeq!([b__, c__, d__, e__, p_], x_)
                && !integerq!(p_)
                && neq!(Atom::num(4) * &p_ + Atom::num(3), 0)
                && eqq!(
                    &b__ * &e__ * (Atom::num(2) * &p_ + Atom::num(1))
                        - &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3)),
                    0
                )
        },
        rhs: {
            let quartic = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_simp(&(&e__ * quartic.pow(&p_ + Atom::num(1))
                    / (&c__ * (Atom::num(4) * &p_ + Atom::num(3)) * x_)), x_)
        },
    ));
}

fn push_rules_rule_1465(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1465,
        source: "Int[(d_+e_.*x_^2)*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          e*(b*x^2+c*x^4)^(p+1)/(c*(4*p+3)*x) - ((b*e*(2*p+1)-c*d*(4*p+3))/(c*(4*p+3))) \\[Star] Int[(b*x^2+c*x^4)^p,x] /;
        FreeQ[{b,c,d,e,p},x] && Not[IntegerQ[p]] && NeQ[4*p+3,0] && NeQ[b*e*(2*p+1)-c*d*(4*p+3),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__, p_],
        when: {
            freeq!([b__, c__, d__, e__, p_], x_)
                && !integerq!(p_)
                && neq!(Atom::num(4) * &p_ + Atom::num(3), 0)
                && neq!(
                    &b__ * &e__ * (Atom::num(2) * &p_ + Atom::num(1))
                        - &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3)),
                    0
                )
        },
        rhs: {
            let denominator = &c__ * (Atom::num(4) * &p_ + Atom::num(3));
            let quartic = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let delta = &b__ * &e__ * (Atom::num(2) * &p_ + Atom::num(1))
                - &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3));
            rubi_simp(&(&e__ * quartic.pow(&p_ + Atom::num(1)) / (&denominator * x_)), x_)
                    - rubi_star(&delta / denominator, rubi_rhs_int(&quartic.pow(&p_), x_))
        },
    ));
}

fn push_rules_rule_1466(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1466,
        source: "Int[(d_+e_.*x_^2)^q_.*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (b*x^2+c*x^4)^FracPart[p]/(x^(2*FracPart[p])*(b+c*x^2)^FracPart[p]) \\[Star] Int[x^(2*p)*(d+e*x^2)^q*(b+c*x^2)^p,x] /;
        FreeQ[{b,c,d,e,p,q},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(q_) * (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [b__, c__, d__, e__, p_, q_, x_],
        optional: [q_, e__, b__, c__],
        x_free: [b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([b__, c__, d__, e__, p_, q_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let quartic = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator =
                x_.pow(Atom::num(2) * &frac_p) * (&b__ + &c__ * x_.pow(2)).pow(&frac_p);
            let recursive_integrand = x_.pow(Atom::num(2) * &p_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&b__ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star(quartic.pow(&frac_p) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1467(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1467,
        source: "Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && IGtQ[q,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [q_, p_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && igtq!(q_, -2)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1468(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1468,
        source: "Int[(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && IGtQ[q,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [q_, p_, e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && igtq!(q_, -2)
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)).pow(&q_) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1469(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1469,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          a^p*x*(d+e*x^2)^(q+1)/d +
          1/d \\[Star] Int[x^2*(d+e*x^2)^q*(d*PolynomialQuotient[(a+b*x^2+c*x^4)^p-a^p,x^2,x]-e*a^p*(2*q+3)),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && ILtQ[q+1/2,0] && LtQ[4*p+2*q+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && iltq!(&q_ + Atom::num(1) / Atom::num(2), 0)
                && ltq!(Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(
                &(quartic.pow(&p_) - a__.pow(&p_)),
                x_.pow(2),
                x_,
            ).rubi_rhs();
            let direct = a__.pow(&p_) * x_ * quadratic.pow(&q_ + Atom::num(1)) / &d__;
            let recursive_integrand = x_.pow(2)
                * quadratic.pow(&q_)
                * (&d__ * quotient - &e__ * a__.pow(&p_) * (Atom::num(2) * &q_ + Atom::num(3)));
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / &d__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1470(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1470,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          a^p*x*(d+e*x^2)^(q+1)/d +
          1/d \\[Star] Int[x^2*(d+e*x^2)^q*(d*PolynomialQuotient[(a+c*x^4)^p-a^p,x^2,x]-e*a^p*(2*q+3)),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && ILtQ[q+1/2,0] && LtQ[4*p+2*q+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && iltq!(&q_ + Atom::num(1) / Atom::num(2), 0)
                && ltq!(Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(
                &(quartic.pow(&p_) - a__.pow(&p_)),
                x_.pow(2),
                x_,
            ).rubi_rhs();
            let direct = a__.pow(&p_) * x_ * quadratic.pow(&q_ + Atom::num(1)) / &d__;
            let recursive_integrand = x_.pow(2)
                * quadratic.pow(&q_)
                * (&d__ * quotient - &e__ * a__.pow(&p_) * (Atom::num(2) * &q_ + Atom::num(3)));
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / &d__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1471(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1471,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x^2+c*x^4)^p,d+e*x^2,x],
                R=Coeff[PolynomialRemainder[(a+b*x^2+c*x^4)^p,d+e*x^2,x],x,0]},
          -R*x*(d+e*x^2)^(q+1)/(2*d*(q+1)) +
          1/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*ExpandToSum[2*d*(q+1)*Qx+R*(2*q+3),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && LtQ[q,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_);
            let Qx = rubi_polynomial_quotient(&quartic_power, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&quartic_power, &quadratic, x_).rubi_rhs();
            let R = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let direct = -&R * x_ * quadratic.pow(&q_ + Atom::num(1)) / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * Qx
                    + &R * (Atom::num(2) * &q_ + Atom::num(3))),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1472(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1472,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+c*x^4)^p,d+e*x^2,x],
                R=Coeff[PolynomialRemainder[(a+c*x^4)^p,d+e*x^2,x],x,0]},
          -R*x*(d+e*x^2)^(q+1)/(2*d*(q+1)) +
          1/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*ExpandToSum[2*d*(q+1)*Qx+R*(2*q+3),x],x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && LtQ[q,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_);
            let Qx = rubi_polynomial_quotient(&quartic_power, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&quartic_power, &quadratic, x_).rubi_rhs();
            let R = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let direct = -&R * x_ * quadratic.pow(&q_ + Atom::num(1)) / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * Qx
                    + &R * (Atom::num(2) * &q_ + Atom::num(3))),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1473(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1473,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          c^p*x^(4*p-1)*(d+e*x^2)^(q+1)/(e*(4*p+2*q+1)) +
          1/(e*(4*p+2*q+1)) \\[Star] Int[(d+e*x^2)^q*ExpandToSum[e*(4*p+2*q+1)*(a+b*x^2+c*x^4)^p-d*c^p*(4*p-1)*x^(4*p-2)-e*c^p*(4*p+2*q+1)*x^(4*p),x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && Not[LtQ[q,-1]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && !ltq!(q_, -1)
        },
        rhs: {
            let denominator = &e__ * (Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let c_p = c__.pow(&p_);
            let balance = Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let direct = &c_p
                * x_.pow(Atom::num(4) * &p_ - Atom::num(1))
                * quadratic.pow(&q_ + Atom::num(1))
                / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&e__ * &balance * quartic.pow(&p_)
                    - &d__
                        * &c_p
                        * (Atom::num(4) * &p_ - Atom::num(1))
                        * x_.pow(Atom::num(4) * &p_ - Atom::num(2))
                    - &e__
                        * &c_p
                        * &balance
                        * x_.pow(Atom::num(4) * &p_)),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_) * expand_to_sum;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1474(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1474,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          c^p*x^(4*p-1)*(d+e*x^2)^(q+1)/(e*(4*p+2*q+1)) +
          1/(e*(4*p+2*q+1)) \\[Star] Int[(d+e*x^2)^q*ExpandToSum[e*(4*p+2*q+1)*(a+c*x^4)^p-d*c^p*(4*p-1)*x^(4*p-2)-e*c^p*(4*p+2*q+1)*x^(4*p),x],x] /;
        FreeQ[{a,c,d,e,q},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && Not[LtQ[q,-1]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [p_, e__, c__],
        x_free: [a__, c__, d__, e__, q_],
        when: {
            freeq!([a__, c__, d__, e__, q_], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(p_, 0)
                && !ltq!(q_, -1)
        },
        rhs: {
            let denominator = &e__ * (Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let c_p = c__.pow(&p_);
            let balance = Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let direct = &c_p
                * x_.pow(Atom::num(4) * &p_ - Atom::num(1))
                * quadratic.pow(&q_ + Atom::num(1))
                / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&e__ * &balance * quartic.pow(&p_)
                    - &d__
                        * &c_p
                        * (Atom::num(4) * &p_ - Atom::num(1))
                        * x_.pow(Atom::num(4) * &p_ - Atom::num(2))
                    - &e__
                        * &c_p
                        * &balance
                        * x_.pow(Atom::num(4) * &p_)),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_) * expand_to_sum;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1475(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1475,
        source: "Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[2*d/e-b/c,2]},
          e/(2*c) \\[Star] Int[1/Simp[d/e+q*x+x^2,x],x] + e/(2*c) \\[Star] Int[1/Simp[d/e-q*x+x^2,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && (GtQ[2*d/e-b/c,0] || Not[LtQ[2*d/e-b/c,0]] && EqQ[d-e*Rt[a/c,2],0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            if freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
            {
                let t = Atom::num(2) * &d__ / &e__ - &b__ / &c__;
                gtq!(t, 0)
                    || (!ltq!(t, 0) && eqq!(&d__ - &e__ * rubi_rt(&(&a__ / &c__), 2), 0))
            } else {
                false
            }
        },
        rhs: {
            let denominator = Atom::num(2) * &c__;
            let q = rubi_rt(&(Atom::num(2) * &d__ / &e__ - &b__ / &c__), 2);
            let first_simp = rubi_simp(&(&d__ / &e__ + &q * x_ + x_.pow(2)), x_);
            let second_simp = rubi_simp(&(&d__ / &e__ - &q * x_ + x_.pow(2)), x_);
            rubi_star(&e__ / &denominator, rubi_rhs_int(&(Atom::num(1) / first_simp), x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&(Atom::num(1) / second_simp), x_))
        },
    ));
}

fn push_rules_rule_1476(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1476,
        source: "Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[2*d/e,2]},
          e/(2*c) \\[Star] Int[1/Simp[d/e+q*x+x^2,x],x] + e/(2*c) \\[Star] Int[1/Simp[d/e-q*x+x^2,x],x]] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2-a*e^2,0] && PosQ[d*e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&d__ * &e__)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__;
            let q = rubi_rt(&(Atom::num(2) * &d__ / &e__), 2);
            let first_simp = rubi_simp(&(&d__ / &e__ + &q * x_ + x_.pow(2)), x_);
            let second_simp = rubi_simp(&(&d__ / &e__ - &q * x_ + x_.pow(2)), x_);
            rubi_star(&e__ / &denominator, rubi_rhs_int(&(Atom::num(1) / first_simp), x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&(Atom::num(1) / second_simp), x_))
        },
    ));
}

fn push_rules_rule_1477(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1477,
        source: "Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2+q/2+c*x^2),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && GtQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &q;
            let first_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            let coefficient_delta = (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / denominator;
            rubi_star(&e__ / Atom::num(2) + &coefficient_delta, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / Atom::num(2) - coefficient_delta, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1478(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1478,
        source: "Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[-2*d/e-b/c,2]},
          e/(2*c*q) \\[Star] Int[(q-2*x)/Simp[d/e+q*x-x^2,x],x] + e/(2*c*q) \\[Star] Int[(q+2*x)/Simp[d/e-q*x-x^2,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && Not[GtQ[b^2-4*a*c,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && !gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-Atom::num(2) * &d__ / &e__ - &b__ / &c__), 2);
            let denominator = Atom::num(2) * &c__ * &q;
            let first_simp = rubi_simp(&(&d__ / &e__ + &q * x_ - x_.pow(2)), x_);
            let second_simp = rubi_simp(&(&d__ / &e__ - &q * x_ - x_.pow(2)), x_);
            rubi_star(&e__ / &denominator, rubi_rhs_int(&((&q - Atom::num(2) * x_) / first_simp), x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&((&q + Atom::num(2) * x_) / second_simp), x_))
        },
    ));
}

fn push_rules_rule_1479(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1479,
        source: "Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[-2*d/e,2]},
          e/(2*c*q) \\[Star] Int[(q-2*x)/Simp[d/e+q*x-x^2,x],x] + e/(2*c*q) \\[Star] Int[(q+2*x)/Simp[d/e-q*x-x^2,x],x]] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2-a*e^2,0] && NegQ[d*e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&d__ * &e__)
        },
        rhs: {
            let q = rubi_rt(&(-Atom::num(2) * &d__ / &e__), 2);
            let denominator = Atom::num(2) * &c__ * &q;
            let first_simp = rubi_simp(&(&d__ / &e__ + &q * x_ - x_.pow(2)), x_);
            let second_simp = rubi_simp(&(&d__ / &e__ - &q * x_ - x_.pow(2)), x_);
            rubi_star(&e__ / &denominator, rubi_rhs_int(&((&q - Atom::num(2) * x_) / first_simp), x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&((&q + Atom::num(2) * x_) / second_simp), x_))
        },
    ));
}

fn push_rules_rule_1480(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1480,
        source: "Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2+q/2+c*x^2),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-a*e^2,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &q;
            let first_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            let coefficient_delta = (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / denominator;
            rubi_star(&e__ / Atom::num(2) + &coefficient_delta, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / Atom::num(2) - coefficient_delta, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1481(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1481,
        source: "Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          (e/2+c*d/(2*q)) \\[Star] Int[1/(-q+c*x^2),x] + (e/2-c*d/(2*q)) \\[Star] Int[1/(q+c*x^2),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2-a*e^2,0] && PosQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(-&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let denominator = Atom::num(2) * &q;
            let first_integrand = Atom::num(1) / (-&q + &c__ * x_.pow(2));
            let second_integrand = Atom::num(1) / (&q + &c__ * x_.pow(2));
            let coefficient_delta = &c__ * &d__ / denominator;
            rubi_star(&e__ / Atom::num(2) + &coefficient_delta, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / Atom::num(2) - coefficient_delta, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1482(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1482,
        source: "Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[a*c,2]},
          (d*q+a*e)/(2*a*c) \\[Star] Int[(q+c*x^2)/(a+c*x^4),x] + (d*q-a*e)/(2*a*c) \\[Star] Int[(q-c*x^2)/(a+c*x^4),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(-&a__ * &c__)
        },
        rhs: {
            let denominator = Atom::num(2) * &a__ * &c__;
            let q = rubi_rt(&(&a__ * &c__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = (&q + &c__ * x_.pow(2)) / &quartic;
            let second_integrand = (&q - &c__ * x_.pow(2)) / quartic;
            rubi_star((&d__ * &q + &a__ * &e__) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star((&d__ * &q - &a__ * &e__) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1483(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1483,
        source: "Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*q*r) \\[Star] Int[(d*r-(d-e*q)*x)/(q-r*x+x^2),x] + 1/(2*c*q*r) \\[Star] Int[(d*r+(d-e*q)*x)/(q+r*x+x^2),x]]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let denominator = Atom::num(2) * &c__ * &q * &r;
            let first_integrand = (&d__ * &r - (&d__ - &e__ * &q) * x_)
                / (&q - &r * x_ + x_.pow(2));
            let second_integrand = (&d__ * &r + (&d__ - &e__ * &q) * x_)
                / (&q + &r * x_ + x_.pow(2));
            let coefficient = Atom::num(1) / denominator;
            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1484(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1484,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(q_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_)
                / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1485(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1485,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q/(a+c*x^4),x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, c__, d__, e__, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && integerq!(q_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_) / (&a__ + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1486(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1486,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          e^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x^2)^q,x] +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x^2)^(q+1)*(c*d-b*e-c*e*x^2)/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let second_integrand = quadratic.pow(&q_ + Atom::num(1))
                * (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(2))
                / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            rubi_star(e__.pow(2) / &denominator, rubi_rhs_int(&quadratic.pow(&q_), x_)) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1487(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1487,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          e^2/(c*d^2+a*e^2) \\[Star] Int[(d+e*x^2)^q,x] +
          c/(c*d^2+a*e^2) \\[Star] Int[(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, c__, d__, e__, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let second_integrand = quadratic.pow(&q_ + Atom::num(1)) * (&d__ - &e__ * x_.pow(2))
                / (&a__ + &c__ * x_.pow(4));
            rubi_star(e__.pow(2) / &denominator, rubi_rhs_int(&quadratic.pow(&q_), x_)) + rubi_star(&c__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1488(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1488,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          2*c/r \\[Star] Int[(d+e*x^2)^q/(b-r+2*c*x^2),x] - 2*c/r \\[Star] Int[(d+e*x^2)^q/(b+r+2*c*x^2),x]] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quadratic_power = (&d__ + &e__ * x_.pow(2)).pow(&q_);
            let first_integrand =
                &quadratic_power / (&b__ - &r + Atom::num(2) * &c__ * x_.pow(2));
            let second_integrand =
                quadratic_power / (&b__ + &r + Atom::num(2) * &c__ * x_.pow(2));
            rubi_star(Atom::num(2) * &c__ / &r, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(2) * &c__ / r, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1489(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1489,
        source: "Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          With[{r=Rt[-a*c,2]},
          -c/(2*r) \\[Star] Int[(d+e*x^2)^q/(r-c*x^2),x] - c/(2*r) \\[Star] Int[(d+e*x^2)^q/(r+c*x^2),x]] /;
        FreeQ[{a,c,d,e,q},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, c__, d__, e__, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, q_],
        when: {
            freeq!([a__, c__, d__, e__, q_], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
        },
        rhs: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            let denominator = Atom::num(2) * &r;
            let quadratic_power = (&d__ + &e__ * x_.pow(2)).pow(&q_);
            let first_integrand = &quadratic_power / (&r - &c__ * x_.pow(2));
            let second_integrand = quadratic_power / (&r + &c__ * x_.pow(2));
            rubi_star(-&c__ / &denominator, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&c__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1490(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1490,
        source: "Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          x*(2*b*e*p+c*d*(4*p+3)+c*e*(4*p+1)*x^2)*(a+b*x^2+c*x^4)^p/(c*(4*p+1)*(4*p+3)) +
          2*p/(c*(4*p+1)*(4*p+3)) \\[Star] Int[Simp[2*a*c*d*(4*p+3)-a*b*e+(2*a*c*e*(4*p+1)+b*c*d*(4*p+3)-b^2*e*(2*p+1))*x^2,x]*
            (a+b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && FractionQ[p] && IntegerQ[2*p]",
        desc: "Trinomial recurrence 1b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
                && fractionq!(p_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = &c__ * (Atom::num(4) * &p_ + Atom::num(1)) * (Atom::num(4) * &p_ + Atom::num(3));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = x_
                * (Atom::num(2) * &b__ * &e__ * &p_
                    + &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3))
                    + &c__ * &e__ * (Atom::num(4) * &p_ + Atom::num(1)) * x_.pow(2))
                * quartic.pow(&p_)
                / &denominator;
            let simp = rubi_simp(
                &(Atom::num(2) * &a__ * &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3))
                    - &a__ * &b__ * &e__
                    + (Atom::num(2) * &a__ * &c__ * &e__ * (Atom::num(4) * &p_ + Atom::num(1))
                        + &b__ * &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3))
                        - b__.pow(2) * &e__ * (Atom::num(2) * &p_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = simp * quartic.pow(&p_ - Atom::num(1));

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1491(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1491,
        source: "Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          x*(d*(4*p+3)+e*(4*p+1)*x^2)*(a+c*x^4)^p/((4*p+1)*(4*p+3)) +
          2*p/((4*p+1)*(4*p+3)) \\[Star] Int[Simp[2*a*d*(4*p+3)+(2*a*e*(4*p+1))*x^2,x]*(a+c*x^4)^(p-1),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && GtQ[p,0] && FractionQ[p] && IntegerQ[2*p]",
        desc: "Trinomial recurrence 1b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
                && fractionq!(p_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = (Atom::num(4) * &p_ + Atom::num(1)) * (Atom::num(4) * &p_ + Atom::num(3));
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = x_
                * (&d__ * (Atom::num(4) * &p_ + Atom::num(3))
                    + &e__ * (Atom::num(4) * &p_ + Atom::num(1)) * x_.pow(2))
                * quartic.pow(&p_)
                / &denominator;
            let simp = rubi_simp(
                &(Atom::num(2) * &a__ * &d__ * (Atom::num(4) * &p_ + Atom::num(3))
                    + Atom::num(2) * &a__ * &e__ * (Atom::num(4) * &p_ + Atom::num(1)) * x_.pow(2)),
                x_,
            );
            let recursive_integrand = simp * quartic.pow(&p_ - Atom::num(1));

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1492(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1492,
        source: "Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          x*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[Simp[(2*p+3)*d*b^2-a*b*e-2*a*c*d*(4*p+5)+(4*p+7)*(d*b-2*a*e)*c*x^2,x]*
            (a+b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Trinomial recurrence 2b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = Atom::num(2)
                * &a__
                * (&p_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = x_
                * (&a__ * &b__ * &e__
                    - &d__ * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                    - &c__ * (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let simp = rubi_simp(
                &((Atom::num(2) * &p_ + Atom::num(3)) * &d__ * b__.pow(2)
                    - &a__ * &b__ * &e__
                    - Atom::num(2) * &a__ * &c__ * &d__ * (Atom::num(4) * &p_ + Atom::num(5))
                    + (Atom::num(4) * &p_ + Atom::num(7))
                        * (&d__ * &b__ - Atom::num(2) * &a__ * &e__)
                        * &c__
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = simp * quartic.pow(&p_ + Atom::num(1));

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1493(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1493,
        source: "Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          -x*(d+e*x^2)*(a+c*x^4)^(p+1)/(4*a*(p+1)) +
          1/(4*a*(p+1)) \\[Star] Int[Simp[d*(4*p+5)+e*(4*p+7)*x^2,x]*(a+c*x^4)^(p+1),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Trinomial recurrence 2b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = Atom::num(4) * &a__ * (&p_ + Atom::num(1));
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = Atom::num(-1) * x_
                * (&d__ + &e__ * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let simp = rubi_simp(
                &(&d__ * (Atom::num(4) * &p_ + Atom::num(5))
                    + &e__ * (Atom::num(4) * &p_ + Atom::num(7)) * x_.pow(2)),
                x_,
            );
            let recursive_integrand = simp * quartic.pow(&p_ + Atom::num(1));

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1494(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1494,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*Sqrt[-c] \\[Star] Int[(d+e*x^2)/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let integrand = (&d__ + &e__ * x_.pow(2))
                / ((&b__ + &q + Atom::num(2) * &c__ * x_.pow(2)).sqrt()
                    * (-&b__ + &q - Atom::num(2) * &c__ * x_.pow(2)).sqrt());
            rubi_star(Atom::num(2) * (-&c__).sqrt(), rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_1495(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1495,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          Sqrt[-c] \\[Star] Int[(d+e*x^2)/(Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
        FreeQ[{a,c,d,e},x] && GtQ[a,0] && LtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && gtq!(a__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let integrand = (&d__ + &e__ * x_.pow(2))
                / ((&q + &c__ * x_.pow(2)).sqrt() * (&q - &c__ * x_.pow(2)).sqrt());
            rubi_star((-&c__).sqrt(), rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_1496(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1496,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,4]},
          -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) +
          d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
         EqQ[e+d*q^2,0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.165.10"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(&c__ / &a__, 0)
                && ltq!(&b__ / &a__, 0)
                && eqq!(&e__ + &d__ * q.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let q_squared = q.pow(2);
            let one_plus = Atom::num(1) + &q_squared * x_.pow(2);
            let direct_denominator = &a__ * &one_plus;
            let elliptic_denominator = &q * quartic.sqrt();
            let parameter_denominator = Atom::num(4) * &c__;
            let direct = -&d__ * x_ * quartic.sqrt() / &direct_denominator;
            let elliptic = rubi_elliptic_e(
                Atom::num(2) * (&q * x_).atan(),
                Atom::num(1) / Atom::num(2) - &b__ * &q_squared / parameter_denominator,
            );
            let second = &d__
                * &one_plus
                * (quartic / (&a__ * one_plus.pow(2))).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) + second
        },
    ));
}

fn push_rules_rule_1497(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1497,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (e+d*q)/q \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NeQ[e+d*q,0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(&c__ / &a__, 0)
                && ltq!(&b__ / &a__, 0)
                && neq!(&e__ + &d__ * &q, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();

            rubi_star((&e__ + &d__ * &q) / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&e__ / &q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1498(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1498,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          e*x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) -
          e*q*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*c*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
            EllipticE[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
         EqQ[2*c*d-e*(b-q),0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.153.2+"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && eqq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q), 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let two_q = Atom::num(2) * &q;
            let x_squared = x_.pow(2);
            let quartic = &a__ + &b__ * &x_squared + &c__ * x_.pow(4);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let two_a_plus = Atom::num(2) * &a__ + &b_plus_q * &x_squared;
            let two_a_minus = Atom::num(2) * &a__ + &b_minus_q * &x_squared;
            let direct_denominator = Atom::num(2) * &c__ * quartic.sqrt();
            let elliptic_denominator =
                Atom::num(2) * &c__ * quartic.sqrt() * (&a__ / &two_a_plus).sqrt();
            let direct = &e__ * x_ * (&b__ + &q + Atom::num(2) * &c__ * &x_squared)
                / &direct_denominator;
            let amplitude = (x_ / (&two_a_plus / &two_q).sqrt()).asin();
            let elliptic = rubi_elliptic_e(amplitude, (&b__ + &q) / &two_q);
            let second = &e__
                * &q
                * (&two_a_minus / &two_a_plus).sqrt()
                * (&two_a_plus / &q).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) - second
        },
    ));
}

fn push_rules_rule_1499(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1499,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) -
          Sqrt[2]*e*q*Sqrt[-a+q*x^2]*Sqrt[(a+q*x^2)/q]/(Sqrt[-a]*c*Sqrt[a+c*x^4])*
            EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
         EqQ[c*d+e*q,0] && IntegerQ[q]] /;
        FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.153.2+"],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            freeq!([a__, c__, d__, e__], x_)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && eqq!(&c__ * &d__ + &e__ * &q, 0)
                && integerq!(q)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let two_q = Atom::num(2) * &q;
            let x_squared = x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let a_plus = &a__ + &q * &x_squared;
            let direct_denominator = &c__ * quartic.sqrt();
            let elliptic_denominator = (-&a__).sqrt() * &c__ * quartic.sqrt();
            let direct = &e__ * x_ * (&q + &c__ * &x_squared) / &direct_denominator;
            let amplitude = (x_ / (&a_plus / &two_q).sqrt()).asin();
            let elliptic = rubi_elliptic_e(amplitude, Atom::num(1) / Atom::num(2));
            let second = Atom::num(2).sqrt()
                * &e__
                * &q
                * (-&a__ + &q * &x_squared).sqrt()
                * (&a_plus / &q).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) - second
        },
    ));
}

fn push_rules_rule_1500(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1500,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) -
          Sqrt[2]*e*q*Sqrt[(a-q*x^2)/(a+q*x^2)]*Sqrt[(a+q*x^2)/q]/(c*Sqrt[a+c*x^4]*Sqrt[a/(a+q*x^2)])*
            EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
         EqQ[c*d+e*q,0]] /;
        FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.153.2+"],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            freeq!([a__, c__, d__, e__], x_)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && eqq!(&c__ * &d__ + &e__ * &q, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let two_q = Atom::num(2) * &q;
            let x_squared = x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let a_plus = &a__ + &q * &x_squared;
            let direct_denominator = &c__ * quartic.sqrt();
            let elliptic_denominator = &c__ * quartic.sqrt() * (&a__ / &a_plus).sqrt();
            let direct = &e__ * x_ * (&q + &c__ * &x_squared) / &direct_denominator;
            let amplitude = (x_ / (&a_plus / &two_q).sqrt()).asin();
            let elliptic = rubi_elliptic_e(amplitude, Atom::num(1) / Atom::num(2));
            let second = Atom::num(2).sqrt()
                * &e__
                * &q
                * ((&a__ - &q * &x_squared) / &a_plus).sqrt()
                * (&a_plus / &q).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) - second
        },
    ));
}

fn push_rules_rule_1501(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1501,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*c*d-e*(b-q))/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c) \\[Star] Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NeQ[2*c*d-e*(b-q),0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && neq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q), 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &c__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand =
                (&b__ - &q + Atom::num(2) * &c__ * x_.pow(2)) / quartic.sqrt();

            rubi_star((Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q)) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1502(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1502,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          (c*d+e*q)/c \\[Star] Int[1/Sqrt[a+c*x^4],x] - e/c \\[Star] Int[(q-c*x^2)/Sqrt[a+c*x^4],x] /;
         NeQ[c*d+e*q,0]] /;
        FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            freeq!([a__, c__, d__, e__], x_)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && neq!(&c__ * &d__ + &e__ * &q, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (&q - &c__ * x_.pow(2)) / quartic.sqrt();

            rubi_star((&c__ * &d__ + &e__ * &q) / &c__, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&e__ / &c__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1503(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1503,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          d \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + e \\[Star] Int[x^2/Sqrt[a+b*x^2+c*x^4],x] /;
         PosQ[(b+q)/a] || PosQ[(b-q)/a]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && (posq!((&b__ + &q) / &a__) || posq!((&b__ - &q) / &a__))
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = x_.pow(2) / quartic.sqrt();

            rubi_star(d__, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(e__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1504(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1504,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          d \\[Star] Int[1/Sqrt[a+c*x^4],x] + e \\[Star] Int[x^2/Sqrt[a+c*x^4],x] /;
        FreeQ[{a,c,d,e},x] && GtQ[-a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && gtq!(-&a__ * &c__, 0) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = x_.pow(2) / quartic.sqrt();

            rubi_star(d__, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(e__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1505(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1505,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -a*e*Rt[-(b+q)/(2*a),2]*Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
            EllipticE[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
         NegQ[(b+q)/a] && EqQ[2*c*d-e*(b+q),0] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ + &q) / &a__)
                && eqq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ + &q), 0)
                && !rubi_simpler_sqrt_q(
                    &(-(&b__ - &q) / (Atom::num(2) * &a__)),
                    &(-(&b__ + &q) / (Atom::num(2) * &a__)),
                )
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let rt = rubi_rt(&(-&b_plus_q / (Atom::num(2) * &a__)), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * quartic.sqrt();
            let amplitude = (&rt * x_).asin();
            let elliptic = rubi_elliptic_e(amplitude, b_minus_q / b_plus_q);

            -&a__ * &e__ * &rt
                    * (Atom::num(1) + (&b__ + &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * (Atom::num(1) + (&b__ - &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * elliptic
                    / denominator
        },
    ));
}

fn push_rules_rule_1506(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1506,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*c*d-e*(b+q))/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c) \\[Star] Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NegQ[(b+q)/a] && NeQ[2*c*d-e*(b+q),0] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ + &q) / &a__)
                && neq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ + &q), 0)
                && !rubi_simpler_sqrt_q(
                    &(-(&b__ - &q) / (Atom::num(2) * &a__)),
                    &(-(&b__ + &q) / (Atom::num(2) * &a__)),
                )
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &c__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand =
                (&b__ + &q + Atom::num(2) * &c__ * x_.pow(2)) / quartic.sqrt();

            rubi_star((Atom::num(2) * &c__ * &d__ - &e__ * (&b__ + &q)) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1507(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1507,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -a*e*Rt[-(b-q)/(2*a),2]*Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
            EllipticE[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
         NegQ[(b-q)/a] && EqQ[2*c*d-e*(b-q),0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.153.5-"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ - &q) / &a__)
                && eqq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q), 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let rt = rubi_rt(&(-&b_minus_q / (Atom::num(2) * &a__)), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * quartic.sqrt();
            let amplitude = (&rt * x_).asin();
            let elliptic = rubi_elliptic_e(amplitude, b_plus_q / b_minus_q);

            -&a__ * &e__ * &rt
                    * (Atom::num(1) + (&b__ - &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * (Atom::num(1) + (&b__ + &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * elliptic
                    / denominator
        },
    ));
}

fn push_rules_rule_1508(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1508,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*c*d-e*(b-q))/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c) \\[Star] Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NegQ[(b-q)/a] && NeQ[2*c*d-e*(b-q),0]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ - &q) / &a__)
                && neq!(Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q), 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &c__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand =
                (&b__ - &q + Atom::num(2) * &c__ * x_.pow(2)) / quartic.sqrt();

            rubi_star((Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q)) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1509(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1509,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,4]},
          -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) +
          d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
         EqQ[e+d*q^2,0]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.165.10"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && eqq!(&e__ + &d__ * q.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let q_squared = q.pow(2);
            let one_plus = Atom::num(1) + &q_squared * x_.pow(2);
            let direct_denominator = &a__ * &one_plus;
            let elliptic_denominator = &q * quartic.sqrt();
            let parameter_denominator = Atom::num(4) * &c__;
            let direct = -&d__ * x_ * quartic.sqrt() / &direct_denominator;
            let elliptic = rubi_elliptic_e(
                Atom::num(2) * (&q * x_).atan(),
                Atom::num(1) / Atom::num(2) - &b__ * &q_squared / parameter_denominator,
            );
            let second = &d__
                * &one_plus
                * (quartic / (&a__ * one_plus.pow(2))).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) + second
        },
    ));
}

fn push_rules_rule_1510(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1510,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,4]},
          -d*x*Sqrt[a+c*x^4]/(a*(1+q^2*x^2)) +
          d*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+c*x^4])*EllipticE[2*ArcTan[q*x],1/2] /;
         EqQ[e+d*q^2,0]] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.165.10"],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && eqq!(&e__ + &d__ * q.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            let quartic = &a__ + &c__ * x_.pow(4);
            let q_squared = q.pow(2);
            let one_plus = Atom::num(1) + &q_squared * x_.pow(2);
            let direct_denominator = &a__ * &one_plus;
            let elliptic_denominator = &q * quartic.sqrt();
            let direct = -&d__ * x_ * quartic.sqrt() / &direct_denominator;
            let elliptic =
                rubi_elliptic_e(Atom::num(2) * (&q * x_).atan(), Atom::num(1) / Atom::num(2));
            let second = &d__
                * &one_plus
                * (quartic / (&a__ * one_plus.pow(2))).sqrt()
                * elliptic
                / elliptic_denominator;

            rubi_simp(&(direct), x_) + second
        },
    ));
}

fn push_rules_rule_1511(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1511,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (e+d*q)/q \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NeQ[e+d*q,0]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && neq!(&e__ + &d__ * &q, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();

            rubi_star((&e__ + &d__ * &q) / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&e__ / &q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1512(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1512,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (e+d*q)/q \\[Star] Int[1/Sqrt[a+c*x^4],x] - e/q \\[Star] Int[(1-q*x^2)/Sqrt[a+c*x^4],x] /;
         NeQ[e+d*q,0]] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && neq!(&e__ + &d__ * &q, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();

            rubi_star((&e__ + &d__ * &q) / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&e__ / &q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1389,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          d/Sqrt[a] \\[Star] Int[Sqrt[1+e*x^2/d]/Sqrt[1-e*x^2/d],x] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && NegQ[c/a] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && negq!(&c__ / &a__)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(a__, 0)
        },
        rhs: {
            let recursive_integrand =
                (Atom::num(1) + &e__ * x_.pow(2) / &d__).sqrt()
                    / (Atom::num(1) - &e__ * x_.pow(2) / &d__).sqrt();
            rubi_star(&d__ / a__.sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1390,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4] \\[Star] Int[(d+e*x^2)/Sqrt[1+c*x^4/a],x] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && NegQ[c/a] && Not[GtQ[a,0]] && Not[LtQ[a,0] && GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && negq!(&c__ / &a__)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !gtq!(a__, 0)
                && !(ltq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let transformed = Atom::num(1) + &c__ * x_.pow(4) / &a__;
            let factor = transformed.sqrt() / quartic.sqrt();
            let recursive_integrand =
                (&d__ + &e__ * x_.pow(2)) / transformed.sqrt();
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1391,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x/(d*Sqrt[a+c*x^4]) -
          (Sqrt[-1+e/d*x^2]*Sqrt[1+e/d*x^2]*EllipticE[ArcSin[(Sqrt[2]*Rt[e/d,2]*x)/Sqrt[-1+e/d*x^2]],1/2])/(Sqrt[2]*d*Rt[e/d,2]*Sqrt[a+c*x^4]) +
          (Sqrt[-1+e/d*x^2]*Sqrt[1+e/d*x^2]*EllipticF[ArcSin[(Sqrt[2]*Rt[e/d,2]*x)/Sqrt[-1+e/d*x^2]],1/2])/(Sqrt[2]*d*Rt[e/d,2]*Sqrt[a+c*x^4]) /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[a,0] && GtQ[c,0] && PosQ[e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && posq!(&e__ / &d__)
        },
        rhs: {
            let ratio = &e__ / &d__;
            let root = rubi_rt(&ratio, 2);
            let quartic_sqrt = (&a__ + &c__ * x_.pow(4)).sqrt();
            let negative_sqrt = (-Atom::num(1) + &ratio * x_.pow(2)).sqrt();
            let positive_sqrt = (Atom::num(1) + &ratio * x_.pow(2)).sqrt();
            let amplitude = (Atom::num(2).sqrt() * &root * x_ / &negative_sqrt).asin();
            let denominator = Atom::num(2).sqrt() * &d__ * &root * &quartic_sqrt;
            let factor = negative_sqrt * positive_sqrt / denominator;
            rubi_simp(&(x_ / (&d__ * &quartic_sqrt)), x_)
                    - rubi_simp(&(&factor * rubi_elliptic_e(&amplitude, Atom::num(1) / 2)), x_)
                    + rubi_simp(&(factor * rubi_elliptic_f(amplitude, Atom::num(1) / 2)), x_)
        },
    ));
}

fn push_rules_rule_1392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1392,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x/(d*Sqrt[a+c*x^4]) -
          x/(d*Sqrt[-2*a]*Sqrt[-e/d*x^2])*EllipticE[ArcSin[Sqrt[-2*a]*Sqrt[-1-e/d*x^2]/Sqrt[a+c*x^4]],1/2] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[a,0] && GtQ[c,0] && NegQ[e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && negq!(&e__ / &d__)
        },
        rhs: {
            let ratio = &e__ / &d__;
            let quartic_sqrt = (&a__ + &c__ * x_.pow(4)).sqrt();
            let factor = x_
                / (&d__ * (-Atom::num(2) * &a__).sqrt() * (-&ratio * x_.pow(2)).sqrt());
            let amplitude = ((-Atom::num(2) * &a__).sqrt()
                * (-Atom::num(1) - &ratio * x_.pow(2)).sqrt()
                / &quartic_sqrt)
                .asin();
            rubi_simp(&(x_ / (&d__ * &quartic_sqrt)), x_)
                    - rubi_simp(&(factor * rubi_elliptic_e(amplitude, Atom::num(1) / 2)), x_)
        },
    ));
}

fn push_rules_rule_1393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1393,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          -x/(e*Sqrt[a+c*x^4]) +
          (Sqrt[-1+e/d*x^2]*Sqrt[1+e/d*x^2]*EllipticE[ArcSin[(Sqrt[2]*Rt[e/d,2]*x)/Sqrt[-1+e/d*x^2]],1/2])/(Sqrt[2]*e*Rt[e/d,2]*Sqrt[a+c*x^4]) /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[a,0] && GtQ[c,0] && PosQ[e/d]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && posq!(&e__ / &d__)
        },
        rhs: {
            let ratio = &e__ / &d__;
            let root = rubi_rt(&ratio, 2);
            let quartic_sqrt = (&a__ + &c__ * x_.pow(4)).sqrt();
            let negative_sqrt = (-Atom::num(1) + &ratio * x_.pow(2)).sqrt();
            let positive_sqrt = (Atom::num(1) + &ratio * x_.pow(2)).sqrt();
            let amplitude = (Atom::num(2).sqrt() * &root * x_ / &negative_sqrt).asin();
            rubi_simp(&(Atom::num(-1) * x_ / (&e__ * &quartic_sqrt)), x_)
                    + rubi_simp(&(negative_sqrt
                        * positive_sqrt
                        * rubi_elliptic_e(amplitude, Atom::num(1) / 2)
                        / (Atom::num(2).sqrt() * &e__ * root * quartic_sqrt)), x_)
        },
    ));
}

fn push_rules_rule_1394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1394,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          -x/(e*Sqrt[a+c*x^4]) +
          x/(e*Sqrt[-2*a]*Sqrt[-e/d*x^2])*EllipticE[ArcSin[(Sqrt[-2*a]*Sqrt[-1-e/d*x^2])/Sqrt[a+c*x^4]],1/2] -
          x/(e*Sqrt[-2*a]*Sqrt[-e/d*x^2])*EllipticF[ArcSin[(Sqrt[-2*a]*Sqrt[-1-e/d*x^2])/Sqrt[a+c*x^4]],1/2] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[a,0] && GtQ[c,0] && NegQ[e/d]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && negq!(&e__ / &d__)
        },
        rhs: {
            let ratio = &e__ / &d__;
            let quartic_sqrt = (&a__ + &c__ * x_.pow(4)).sqrt();
            let factor = x_
                / (&e__ * (-Atom::num(2) * &a__).sqrt() * (-&ratio * x_.pow(2)).sqrt());
            let amplitude = ((-Atom::num(2) * &a__).sqrt()
                * (-Atom::num(1) - &ratio * x_.pow(2)).sqrt()
                / &quartic_sqrt)
                .asin();
            rubi_simp(&(Atom::num(-1) * x_ / (&e__ * quartic_sqrt)), x_)
                    + rubi_simp(&(&factor * rubi_elliptic_e(&amplitude, Atom::num(1) / 2)), x_)
                    - rubi_simp(&(factor * rubi_elliptic_f(amplitude, Atom::num(1) / 2)), x_)
        },
    ));
}

fn push_rules_rule_1513(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1513,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[-c/a,2]},
          (d*q-e)/q \\[Star] Int[1/Sqrt[a+c*x^4],x] + e/q \\[Star] Int[(1+q*x^2)/Sqrt[a+c*x^4],x]] /;
        FreeQ[{a,c,d,e},x] && NegQ[c/a] && NeQ[c*d^2+a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && negq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(-&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / quartic.sqrt();

            rubi_star((&d__ * &q - &e__) / &q, rubi_rhs_int(&first_integrand, x_)) + rubi_star(&e__ / &q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1514(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1514,
        source: "Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4] \\[Star]
            Int[(d+e*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let b_plus_q = &b__ + &q;
            let first_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_q).sqrt();
            let second_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_q).sqrt();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = quartic.sqrt();
            let recursive_integrand = (&d__ + &e__ * x_.pow(2)) / (&first_sqrt * &second_sqrt);
            let factor = first_sqrt * second_sqrt / denominator;

            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1515(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1515,
        source: "Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)) * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1516(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1516,
        source: "Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1517(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1517,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{f=Coeff[PolynomialRemainder[(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
                g=Coeff[PolynomialRemainder[(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^2+c*x^4)^(p+1)*
            ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
              b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g+c*(4*p+7)*(b*f-2*a*g)*x^2,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[q,1] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(q_, 1)
                && ltq!(p_, -1)
        },
        rhs: {
            let denominator =
                Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic_power = quadratic.pow(&q_);
            let polynomial_remainder =
                rubi_polynomial_remainder(&quadratic_power, &quartic, x_).rubi_rhs();
            let f = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let g = rubi_coeff(&polynomial_remainder, x_, 2).rubi_rhs();
            let polynomial_quotient =
                rubi_polynomial_quotient(&quadratic_power, &quartic, x_).rubi_rhs();
            let direct_numerator =
                &a__ * &b__ * &g - &f * (b__.pow(2) - Atom::num(2) * &a__ * &c__) - &c__ * (&b__ * &f - Atom::num(2) * &a__ * &g) * x_.pow(2);
            let direct =
                x_ * quartic.pow(&p_ + Atom::num(1)) * direct_numerator / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2)
                * &a__
                * (&p_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(4) * &a__ * &c__)
                * polynomial_quotient
                + b__.pow(2) * &f * (Atom::num(2) * &p_ + Atom::num(3))
                - Atom::num(2) * &a__ * &c__ * &f * (Atom::num(4) * &p_ + Atom::num(5))
                - &a__ * &b__ * &g
                + &c__
                    * (Atom::num(4) * &p_ + Atom::num(7))
                    * (&b__ * &f - Atom::num(2) * &a__ * &g)
                    * x_.pow(2)),
                x_,
            );
            let recursive_integrand = quartic.pow(&p_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1518(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1518,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          e^q*x^(2*q-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(4*p+2*q+1)) +
          1/(c*(4*p+2*q+1)) \\[Star] Int[(a+b*x^2+c*x^4)^p*
            ExpandToSum[c*(4*p+2*q+1)*(d+e*x^2)^q-a*(2*q-3)*e^q*x^(2*q-4)-b*(2*p+2*q-1)*e^q*x^(2*q-2)-c*(4*p+2*q+1)*e^q*x^(2*q),x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[q,1]",
        desc: "Algebraic expansion and",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(q_, 1)
        },
        rhs: {
            let balance = Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let denominator = &c__ * &balance;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let e_q = e__.pow(&q_);
            let direct = &e_q
                * x_.pow(Atom::num(2) * &q_ - Atom::num(3))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * &balance * quadratic.pow(&q_)
                    - &a__ * (Atom::num(2) * &q_ - Atom::num(3)) * &e_q * x_.pow(Atom::num(2) * &q_ - Atom::num(4))
                    - &b__ * (Atom::num(2) * &p_ + Atom::num(2) * &q_ - Atom::num(1)) * &e_q * x_.pow(Atom::num(2) * &q_ - Atom::num(2))
                    - &c__ * &balance * &e_q * x_.pow(Atom::num(2) * &q_)),
                x_,
            );
            let recursive_integrand = quartic.pow(&p_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1519(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1519,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
          e^q*x^(2*q-3)*(a+c*x^4)^(p+1)/(c*(4*p+2*q+1)) +
          1/(c*(4*p+2*q+1)) \\[Star] Int[(a+c*x^4)^p*
            ExpandToSum[c*(4*p+2*q+1)*(d+e*x^2)^q-a*(2*q-3)*e^q*x^(2*q-4)-c*(4*p+2*q+1)*e^q*x^(2*q),x],x] /;
        FreeQ[{a,c,d,e,p},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[q,1]",
        desc: "Algebraic expansion and",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, p_],
        when: {
            freeq!([a__, c__, d__, e__, p_], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(q_, 1)
        },
        rhs: {
            let balance = Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let denominator = &c__ * &balance;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let e_q = e__.pow(&q_);
            let direct = &e_q
                * x_.pow(Atom::num(2) * &q_ - Atom::num(3))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * &balance * quadratic.pow(&q_)
                    - &a__ * (Atom::num(2) * &q_ - Atom::num(3)) * &e_q * x_.pow(Atom::num(2) * &q_ - Atom::num(4))
                    - &c__ * &balance * &e_q * x_.pow(Atom::num(2) * &q_)),
                x_,
            );
            let recursive_integrand = quartic.pow(&p_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1520(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1520,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          -c/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+b*x^2+c*x^4],x] + Int[(2*a+b*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let second_integrand =
                (Atom::num(2) * &a__ + &b__ * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star(-&c__ / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) + rubi_rhs_int(&second_integrand, x_)
        },
    ));
}

fn push_rules_rule_1521(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1521,
        source: "Int[Sqrt[a_+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          -c/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+c*x^4],x] + 2*a \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let second_integrand = Atom::num(1) / (quadratic * quartic.sqrt());

            rubi_star(-&c__ / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(2) * &a__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1522(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1522,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          1/(2*e) \\[Star] Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] -
          1/(2*e) \\[Star] Int[(b*d-2*a*e-d*q+(2*c*d-b*e-e*q)*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let coefficient = Atom::num(1) / (Atom::num(2) * &e__);
            let first_integrand =
                (&b__ - &q + Atom::num(2) * &c__ * x_.pow(2)) / quartic.sqrt();
            let second_integrand = (&b__ * &d__
                - Atom::num(2) * &a__ * &e__
                - &d__ * &q
                + (Atom::num(2) * &c__ * &d__ - &b__ * &e__ - &e__ * &q)
                    * x_.pow(2))
                / (quadratic * quartic.sqrt());

            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1523(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1523,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (c*d^2-b*d*e+a*e^2)/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] -
          1/(e*(e-d*q)) \\[Star] Int[(c*d-b*e+a*e*q-(c*e-a*d*q^3)*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &e__ * (&e__ - &d__ * &q);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let first_integrand = (Atom::num(1) + &q * x_.pow(2))
                / (quadratic * quartic.sqrt());
            let second_integrand = (&c__ * &d__ - &b__ * &e__ + &a__ * &e__ * &q
                - (&c__ * &e__ - &a__ * &d__ * q.pow(3)) * x_.pow(2))
                / quartic.sqrt();

            rubi_star(&resultant / &denominator, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1524(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1524,
        source: "Int[Sqrt[a_+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (c*d^2+a*e^2)/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] -
          1/(e*(e-d*q)) \\[Star] Int[(c*d+a*e*q-(c*e-a*d*q^3)*x^2)/Sqrt[a+c*x^4],x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &e__ * (&e__ - &d__ * &q);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let first_integrand = (Atom::num(1) + &q * x_.pow(2))
                / (quadratic * quartic.sqrt());
            let second_integrand = (&c__ * &d__ + &a__ * &e__ * &q
                - (&c__ * &e__ - &a__ * &d__ * q.pow(3)) * x_.pow(2))
                / quartic.sqrt();

            rubi_star(&resultant / &denominator, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1525(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1525,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] -
          1/e^2 \\[Star] Int[(c*d-b*e-c*e*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let first_integrand = Atom::num(1) / (quadratic * quartic.sqrt());
            let second_integrand =
                (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(2))
                    / quartic.sqrt();

            rubi_star(&resultant / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / e__.pow(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1526(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1526,
        source: "Int[Sqrt[a_+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
          (c*d^2+a*e^2)/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] -
          1/e^2 \\[Star] Int[(c*d-c*e*x^2)/Sqrt[a+c*x^4],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let first_integrand = Atom::num(1) / (quadratic * quartic.sqrt());
            let second_integrand =
                (&c__ * &d__ - &c__ * &e__ * x_.pow(2)) / quartic.sqrt();

            rubi_star(&resultant / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / e__.pow(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1527(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1527,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -1/e^2 \\[Star] Int[(c*d-b*e-c*e*x^2)*(a+b*x^2+c*x^4)^(p-1),x] +
          (c*d^2-b*d*e+a*e^2)/e^2 \\[Star] Int[(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p-1/2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand =
                (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = quartic.pow(&p_ - Atom::num(1)) / quadratic;

            rubi_star(-Atom::num(1) / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) + rubi_star((&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2))
                        / e__.pow(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1528(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1528,
        source: "Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -1/e^2 \\[Star] Int[(c*d-c*e*x^2)*(a+c*x^4)^(p-1),x] +
          (c*d^2+a*e^2)/e^2 \\[Star] Int[(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p-1/2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand =
                (&c__ * &d__ - &c__ * &e__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = quartic.pow(&p_ - Atom::num(1)) / quadratic;

            rubi_star(-Atom::num(1) / e__.pow(2), rubi_rhs_int(&first_integrand, x_)) + rubi_star((&c__ * d__.pow(2) + &a__ * e__.pow(2)) / e__.pow(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1529(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1529,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(2*c*d-e*(b+q))*(c*d^2-b*d*e+a*e^2)^(p-1/2)/(4*c*e^(2*p)) \\[Star]
            Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          1/(4*c*e^(2*p)) \\[Star] Int[(1/Sqrt[a+b*x^2+c*x^4])*
              ExpandToSum[(4*c*e^(2*p)*(a+b*x^2+c*x^4)^(p+1/2)+(2*c*d-e*(b+q))*(c*d^2-b*d*e+a*e^2)^(p-1/2)*(b-q+2*c*x^2))/(d+e*x^2),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p-1/2,0] && PosQ[b^2-4*a*c] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let e_power = e__.pow(Atom::num(2) * &p_);
            let linear = &b__ - &q + Atom::num(2) * &c__ * x_.pow(2);
            let multiplier = Atom::num(2) * &c__ * &d__ - &e__ * (&b__ + &q);
            let first_integrand = &linear / (&quadratic * quartic.sqrt());
            let first_coefficient = -&multiplier
                * resultant.pow(&p_ - Atom::num(1) / Atom::num(2))
                / (Atom::num(4) * &c__ * &e_power);
            let expanded = rubi_expand_to_sum(
                &((Atom::num(4)
                    * &c__
                    * &e_power
                    * quartic.pow(&p_ + Atom::num(1) / Atom::num(2))
                    + &multiplier
                        * resultant.pow(&p_ - Atom::num(1) / Atom::num(2))
                        * &linear)
                    / quadratic),
                x_,
            );
            let second_integrand = expanded / quartic.sqrt();

            rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / (Atom::num(4) * &c__ * e_power), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1530(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1530,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          1/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4]*
              ExpandToSum[(e^(2*p)*(c*d^2-a*e^2)*(a+b*x^2+c*x^4)^(p+1/2) +
                (c*d^2-b*d*e+a*e^2)^(p+1/2)*(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p-1/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let difference = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let e_power = e__.pow(Atom::num(2) * &p_);
            let linear = &a__ * &d__ * &q
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &q) * x_.pow(2);
            let first_integrand = &linear / (&quadratic * quartic.sqrt());
            let first_coefficient = -resultant.pow(&p_ + Atom::num(1) / Atom::num(2))
                / (&e_power * &difference);
            let expanded = rubi_expand_to_sum(
                &((&e_power
                    * &difference
                    * quartic.pow(&p_ + Atom::num(1) / Atom::num(2))
                    + resultant.pow(&p_ + Atom::num(1) / Atom::num(2)) * &linear)
                    / quadratic),
                x_,
            );
            let second_integrand = expanded / quartic.sqrt();

            rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / (e_power * difference), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1531(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1531,
        source: "Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          1/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[1/Sqrt[a+c*x^4]*
              ExpandToSum[(e^(2*p)*(c*d^2-a*e^2)*(a+c*x^4)^(p+1/2) +
                (c*d^2+a*e^2)^(p+1/2)*(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p-1/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let difference = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let e_power = e__.pow(Atom::num(2) * &p_);
            let linear = &a__ * &d__ * &q
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &q) * x_.pow(2);
            let first_integrand = &linear / (&quadratic * quartic.sqrt());
            let first_coefficient = -resultant.pow(&p_ + Atom::num(1) / Atom::num(2))
                / (&e_power * &difference);
            let expanded = rubi_expand_to_sum(
                &((&e_power
                    * &difference
                    * quartic.pow(&p_ + Atom::num(1) / Atom::num(2))
                    + resultant.pow(&p_ + Atom::num(1) / Atom::num(2)) * &linear)
                    / quadratic),
                x_,
            );
            let second_integrand = expanded / quartic.sqrt();

            rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / (e_power * difference), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1532(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1532,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          1/e^(2*p+1) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4]*ExpandToSum[(e^(2*p+1)*(a+b*x^2+c*x^4)^(p+1/2)-(c*d^2-b*d*e+a*e^2)^(p+1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p-1/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let e_power = e__.pow(Atom::num(2) * &p_ + Atom::num(1));
            let resultant_power = resultant.pow(&p_ + Atom::num(1) / Atom::num(2));
            let first_integrand = Atom::num(1) / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((&e_power * quartic.pow(&p_ + Atom::num(1) / Atom::num(2))
                    - &resultant_power)
                    / quadratic),
                x_,
            );
            let second_integrand = expanded / quartic.sqrt();

            rubi_star(&resultant_power / &e_power, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / e_power, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1533(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1533,
        source: "Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          1/e^(2*p+1) \\[Star] Int[1/Sqrt[a+c*x^4]*ExpandToSum[(e^(2*p+1)*(a+c*x^4)^(p+1/2)-(c*d^2+a*e^2)^(p+1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p-1/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let e_power = e__.pow(Atom::num(2) * &p_ + Atom::num(1));
            let resultant_power = resultant.pow(&p_ + Atom::num(1) / Atom::num(2));
            let first_integrand = Atom::num(1) / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((&e_power * quartic.pow(&p_ + Atom::num(1) / Atom::num(2))
                    - &resultant_power)
                    / quadratic),
                x_,
            );
            let second_integrand = expanded / quartic.sqrt();

            rubi_star(&resultant_power / &e_power, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / e_power, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1534(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1534,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          1/(2*d) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*d) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star(Atom::num(1) / (Atom::num(2) * &d__), rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(Atom::num(1) / (Atom::num(2) * &d__), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1535(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1535,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          1/(2*d) \\[Star] Int[1/Sqrt[a+c*x^4],x] + 1/(2*d) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star(Atom::num(1) / (Atom::num(2) * &d__), rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(Atom::num(1) / (Atom::num(2) * &d__), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1536(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1536,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*Sqrt[-c] \\[Star] Int[1/((d+e*x^2)*Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_sqrt = (&b__ + &q + Atom::num(2) * &c__ * x_.pow(2)).sqrt();
            let second_sqrt = (-&b__ + &q - Atom::num(2) * &c__ * x_.pow(2)).sqrt();
            let recursive_integrand = Atom::num(1) / (quadratic * first_sqrt * second_sqrt);
            rubi_star(Atom::num(2) * (-&c__).sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1537(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1537,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          Sqrt[-c] \\[Star] Int[1/((d+e*x^2)*Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && GtQ[a,0] && LtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(a__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_sqrt = (&q + &c__ * x_.pow(2)).sqrt();
            let second_sqrt = (&q - &c__ * x_.pow(2)).sqrt();
            let recursive_integrand = Atom::num(1) / (quadratic * first_sqrt * second_sqrt);
            rubi_star((-&c__).sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1538(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1538,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/(2*c*d-e*(b-q)) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/(2*c*d-e*(b-q)) \\[Star] Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[LtQ[c,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let denominator = Atom::num(2) * &c__ * &d__ - &e__ * (&b__ - &q);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let second_integrand =
                (&b__ - &q + Atom::num(2) * &c__ * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star(Atom::num(2) * &c__ / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) - rubi_star(&e__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1539(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1539,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          c/(c*d+e*q) \\[Star] Int[1/Sqrt[a+c*x^4],x] + e/(c*d+e*q) \\[Star] Int[(q-c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && GtQ[-a*c,0] && Not[LtQ[c,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(-&a__ * &c__, 0)
                && !ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let denominator = &c__ * &d__ + &e__ * &q;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let second_integrand = (&q - &c__ * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star(&c__ / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(&e__ / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1540(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1540,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (c*d+a*e*q)/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] -
          (a*e*(e+d*q))/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let second_integrand =
                (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star((&c__ * &d__ + &a__ * &e__ * &q) / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) - rubi_star(&a__ * &e__ * (&e__ + &d__ * &q) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1541(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1541,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (c*d+a*e*q)/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+c*x^4],x] -
          (a*e*(e+d*q))/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let second_integrand =
                (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());

            rubi_star((&c__ * &d__ + &a__ * &e__ * &q) / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) - rubi_star(&a__ * &e__ * (&e__ + &d__ * &q) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1542(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1542,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[-c/a,4]},
          1/(d*Sqrt[a]*q)*EllipticPi[-e/(d*q^2),ArcSin[q*x],-1]] /;
        FreeQ[{a,c,d,e},x] && NegQ[c/a] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && negq!(&c__ / &a__) && gtq!(a__, 0) },
        rhs: {
            let q = rubi_rt(&(-&c__ / &a__), 4);
            let direct_denominator = &d__ * a__.sqrt() * &q;
            let parameter_denominator = &d__ * q.pow(2);
            rubi_simp(&(rubi_elliptic_pi(-&e__ / parameter_denominator, (&q * x_).asin(), -Atom::num(1)) / direct_denominator), x_)
        },
    ));
}

fn push_rules_rule_1543(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1543,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4] \\[Star] Int[1/((d+e*x^2)*Sqrt[1+c*x^4/a]),x] /;
        FreeQ[{a,c,d,e},x] && NegQ[c/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && negq!(&c__ / &a__) && !gtq!(a__, 0) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = quartic.sqrt();
            let transformed = Atom::num(1) + &c__ * x_.pow(4) / &a__;
            let recursive_integrand = Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * transformed.sqrt());

            rubi_star(transformed.sqrt() / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1544(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1544,
        source: "Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4] \\[Star]
            Int[1/((d+e*x^2)*Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NegQ[c/a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let b_plus_q = &b__ + &q;
            let first_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_q).sqrt();
            let second_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_q).sqrt();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = quartic.sqrt();
            let recursive_integrand =
                Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * &first_sqrt * &second_sqrt);

            rubi_star(first_sqrt * second_sqrt / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1545(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1545,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(c*d-b*e-c*e*x^2)*(a+b*x^2+c*x^4)^p,x] +
          e^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && (EqQ[c*d^2-a*e^2,0] || NiceSqrtQ[b^2-4*a*c])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && (eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                    || rubi_nice_sqrt_q(&(b__.pow(2) - Atom::num(4) * &a__ * &c__)))
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand =
                (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = quartic.pow(&p_ + Atom::num(1)) / quadratic;

            rubi_star(Atom::num(1) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(e__.pow(2) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1546(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1546,
        source: "Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          1/(c*d^2+a*e^2) \\[Star] Int[(c*d-c*e*x^2)*(a+c*x^4)^p,x] +
          e^2/(c*d^2+a*e^2) \\[Star] Int[(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0] && EqQ[c*d^2-a*e^2,0] && (EqQ[c*d^2-a*e^2,0] || NiceSqrtQ[-a*c])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && (eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                    || rubi_nice_sqrt_q(&(-&a__ * &c__)))
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = (&c__ * &d__ - &c__ * &e__ * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = quartic.pow(&p_ + Atom::num(1)) / quadratic;

            rubi_star(Atom::num(1) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(e__.pow(2) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1547(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1547,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
          -(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (c*d^2-b*d*e+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[(a+b*x^2+c*x^4)^p*
              ExpandToSum[((Rt[c/a,2]*d-e)*(c*d^2-b*d*e+a*e^2)^(-p-1/2)+e^(-2*p)*(1+Rt[c/a,2]*x^2)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num(1) / Atom::num(2);
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let resultant_power = resultant.pow(&p_ + &half);
            let inverse_power = -&p_ - &half;
            let e_power = e__.pow(Atom::num(2) * &p_);
            let difference = &q * &d__ - &e__;
            let linear = Atom::num(1) + &q * x_.pow(2);
            let first_integrand = &linear / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((&difference * resultant.pow(&inverse_power)
                    + e__.pow(-Atom::num(2) * &p_) * &linear * quartic.pow(&inverse_power))
                    / quadratic),
                x_,
            );
            let second_integrand = quartic.pow(&p_) * expanded;

            rubi_star(-&resultant_power / (&e_power * &difference), rubi_rhs_int(&first_integrand, x_)) + rubi_star(&resultant_power / difference, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1548(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1548,
        source: "Int[(a_+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
          -(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (c*d^2+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[(a+c*x^4)^p*
              ExpandToSum[((Rt[c/a,2]*d-e)*(c*d^2+a*e^2)^(-p-1/2)+e^(-2*p)*(1+Rt[c/a,2]*x^2)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [c__, d__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num(1) / Atom::num(2);
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let resultant_power = resultant.pow(&p_ + &half);
            let inverse_power = -&p_ - &half;
            let e_power = e__.pow(Atom::num(2) * &p_);
            let difference = &q * &d__ - &e__;
            let linear = Atom::num(1) + &q * x_.pow(2);
            let first_integrand = &linear / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((&difference * resultant.pow(&inverse_power)
                    + e__.pow(-Atom::num(2) * &p_) * &linear * quartic.pow(&inverse_power))
                    / quadratic),
                x_,
            );
            let second_integrand = quartic.pow(&p_) * expanded;

            rubi_star(-&resultant_power / (&e_power * &difference), rubi_rhs_int(&first_integrand, x_)) + rubi_star(&resultant_power / difference, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1549(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1549,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (c*d^2-b*d*e+a*e^2)^(p+1/2) \\[Star] Int[(a+b*x^2+c*x^4)^p*
              ExpandToSum[((c*d^2-b*d*e+a*e^2)^(-p-1/2)-e^(-2*p-1)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let resultant_power = resultant.pow(&p_ + &half);
            let inverse_power = -&p_ - &half;
            let e_power_exponent = Atom::num(2) * &p_ + Atom::num(1);
            let first_integrand = Atom::num(1) / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((resultant.pow(&inverse_power)
                    - e__.pow(-&e_power_exponent) * quartic.pow(&inverse_power))
                    / quadratic),
                x_,
            );
            let second_integrand = quartic.pow(&p_) * expanded;

            rubi_star(&resultant_power / e__.pow(&e_power_exponent), rubi_rhs_int(&first_integrand, x_)) + rubi_star(resultant_power, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1550(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1550,
        source: "Int[(a_+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
          (c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (c*d^2+a*e^2)^(p+1/2) \\[Star] Int[(a+c*x^4)^p*
              ExpandToSum[((c*d^2+a*e^2)^(-p-1/2)-e^(-2*p-1)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [c__, d__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let resultant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let resultant_power = resultant.pow(&p_ + &half);
            let inverse_power = -&p_ - &half;
            let e_power_exponent = Atom::num(2) * &p_ + Atom::num(1);
            let first_integrand = Atom::num(1) / (&quadratic * quartic.sqrt());
            let expanded = rubi_expand_to_sum(
                &((resultant.pow(&inverse_power)
                    - e__.pow(-&e_power_exponent) * quartic.pow(&inverse_power))
                    / quadratic),
                x_,
            );
            let second_integrand = quartic.pow(&p_) * expanded;

            rubi_star(&resultant_power / e__.pow(&e_power_exponent), rubi_rhs_int(&first_integrand, x_)) + rubi_star(resultant_power, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1551(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1551,
        source: "Int[(d_+e_.*x_^2)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          -e^2*x*(d+e*x^2)^(q+1)*Sqrt[a+b*x^2+c*x^4]/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x^2)^(q+1)/Sqrt[a+b*x^2+c*x^4]*
            Simp[a*e^2*(2*q+3)+2*d*(c*d-b*e)*(q+1)-2*e*(c*d*(q+1)-b*e*(q+2))*x^2+c*e^2*(2*q+5)*x^4,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [a__, b__, c__, d__, e__, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * &invariant;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = -e__.pow(2)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                * quartic.sqrt()
                / &denominator;
            let simp = rubi_simp(
                &(&a__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(3))
                    + Atom::num(2) * &d__ * (&c__ * &d__ - &b__ * &e__) * (&q_ + Atom::num(1))
                    - Atom::num(2)
                        * &e__
                        * (&c__ * &d__ * (&q_ + Atom::num(1)) - &b__ * &e__ * (&q_ + Atom::num(2)))
                        * x_.pow(2)
                    + &c__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * simp / quartic.sqrt();

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1552(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1552,
        source: "Int[(d_+e_.*x_^2)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          -e^2*x*(d+e*x^2)^(q+1)*Sqrt[a+c*x^4]/(2*d*(q+1)*(c*d^2+a*e^2)) +
          1/(2*d*(q+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x^2)^(q+1)/Sqrt[a+c*x^4]*
            Simp[a*e^2*(2*q+3)+2*c*d^2*(q+1)-2*e*c*d*(q+1)*x^2+c*e^2*(2*q+5)*x^4,x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + c__ * x_.pow(4)).sqrt(),
        with: [a__, c__, d__, e__, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * &invariant;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = -e__.pow(2)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                * quartic.sqrt()
                / &denominator;
            let simp = rubi_simp(
                &(&a__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(3))
                    + Atom::num(2) * &c__ * d__.pow(2) * (&q_ + Atom::num(1))
                    - Atom::num(2) * &e__ * &c__ * &d__ * (&q_ + Atom::num(1)) * x_.pow(2)
                    + &c__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * simp / quartic.sqrt();

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1553(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1553,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2)^2,x_Symbol] :=
          With[{q=Rt[e/d,2]},
          c*(d+e*x^2)*Sqrt[(e^2*(a+b*x^2+c*x^4))/(c*(d+e*x^2)^2)]/(2*d*e^2*q*Sqrt[a+b*x^2+c*x^4])*
            EllipticE[2*ArcTan[q*x],(2*c*d-b*e)/(4*c*d)]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[c*d^2-a*e^2,0] && PosQ[e/d]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt() / (d__ + e__ * x_.pow(2)).pow(2),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&e__ / &d__)
        },
        rhs: {
            let q = rubi_rt(&(&e__ / &d__), 2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct_denominator = Atom::num(2) * &d__ * e__.pow(2) * &q * quartic.sqrt();
            let sqrt_denominator = &c__ * quadratic.pow(2);
            let parameter_denominator = Atom::num(4) * &c__ * &d__;
            let elliptic = rubi_elliptic_e(
                Atom::num(2) * (&q * x_).atan(),
                (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / parameter_denominator,
            );
            let sqrt_factor = (e__.pow(2) * &quartic / sqrt_denominator).sqrt();

            rubi_simp(&(&c__ * quadratic * sqrt_factor * elliptic / direct_denominator), x_)
        },
    ));
}

fn push_rules_rule_1554(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1554,
        source: "Int[(d_+e_.*x_^2)^q_*Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          -x*(d+e*x^2)^(q+1)*Sqrt[a+b*x^2+c*x^4]/(2*d*(q+1)) +
          1/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*(a*(2*q+3)+2*b*(q+2)*x^2+c*(2*q+5)*x^4)/Sqrt[a+b*x^2+c*x^4],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[q,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [a__, b__, c__, d__, e__, q_, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let direct =
                Atom::num(-1) * x_ * quadratic.pow(&q_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1))
                * (&a__ * (Atom::num(2) * &q_ + Atom::num(3))
                    + Atom::num(2) * &b__ * (&q_ + Atom::num(2)) * x_.pow(2)
                    + &c__ * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4))
                / quartic.sqrt();

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1555(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 1555,
        source: "Int[(d_+e_.*x_^2)^q_*Sqrt[a_+c_.*x_^4],x_Symbol] :=
          -x*(d+e*x^2)^(q+1)*Sqrt[a+c*x^4]/(2*d*(q+1)) +
          1/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*(a*(2*q+3)+c*(2*q+5)*x^4)/Sqrt[a+c*x^4],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[q,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).sqrt(),
        with: [a__, c__, d__, e__, q_, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let direct =
                Atom::num(-1) * x_ * quadratic.pow(&q_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1))
                * (&a__ * (Atom::num(2) * &q_ + Atom::num(3))
                    + &c__ * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4))
                / quartic.sqrt();

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1556(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1556,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Module[{aa,bb,cc},
          Int[ReplaceAll[ExpandIntegrand[1/Sqrt[aa+bb*x^2+cc*x^4],(d+e*x^2)^q*(aa+bb*x^2+cc*x^4)^(p+1/2),x],{aa->a,bb->b,cc->c}],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[q,0] && IntegerQ[p+1/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(q_, 0)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let aa_guard = fresh_substitution_symbol().unwrap();
            let bb_guard = fresh_substitution_symbol().unwrap();
            let cc_guard = fresh_substitution_symbol().unwrap();
            let aa = aa_guard.symbol();
            let bb = bb_guard.symbol();
            let cc = cc_guard.symbol();
            let aa_atom = Atom::var(aa);
            let bb_atom = Atom::var(bb);
            let cc_atom = Atom::var(cc);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &aa_atom + &bb_atom * x_.pow(2) + &cc_atom * x_.pow(4);
            let u = Atom::num(1) / quartic.sqrt();
            let v_expr = quadratic.pow(&q_) * quartic.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);
            let replaced = substitute_symbol(
                &substitute_symbol(&substitute_symbol(&expanded, aa, &a__), bb, &b__),
                cc,
                &c__,
            );

            rubi_rhs_int(&replaced, x_)
        },
    ));
}

fn push_rules_rule_1557(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1557,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Module[{aa,cc},
          Int[ReplaceAll[ExpandIntegrand[1/Sqrt[aa+cc*x^4],(d+e*x^2)^q*(aa+cc*x^4)^(p+1/2),x],{aa->a,cc->c}],x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[q,0] && IntegerQ[p+1/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(q_, 0)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let aa_guard = fresh_substitution_symbol().unwrap();
            let cc_guard = fresh_substitution_symbol().unwrap();
            let aa = aa_guard.symbol();
            let cc = cc_guard.symbol();
            let aa_atom = Atom::var(aa);
            let cc_atom = Atom::var(cc);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &aa_atom + &cc_atom * x_.pow(4);
            let u = Atom::num(1) / quartic.sqrt();
            let v_expr = quadratic.pow(&q_) * quartic.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);
            let replaced = substitute_symbol(&substitute_symbol(&expanded, aa, &a__), cc, &c__);

            rubi_rhs_int(&replaced, x_)
        },
    ));
}

fn push_rules_rule_1558(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1558,
        source: "Int[Sqrt[d_+e_.*x_^2]/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4] \\[Star]
            Int[Sqrt[d+e*x^2]/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).sqrt()
            / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_sqrt =
                (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / (&b__ - &q)).sqrt();
            let second_sqrt =
                (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / (&b__ + &q)).sqrt();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand =
                (&d__ + &e__ * x_.pow(2)).sqrt() / (&first_sqrt * &second_sqrt);

            rubi_star(first_sqrt * second_sqrt / quartic.sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1559(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1559,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          1/(2*Sqrt[a]*Sqrt[d]*Rt[-e/d,2])*EllipticF[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && GtQ[a,0] && GtQ[d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * &d__ - &b__ * &e__, 0)
                && gtq!(a__, 0)
                && gtq!(d__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&e__ / &d__), 2);
            let direct_denominator = Atom::num(2) * a__.sqrt() * d__.sqrt() * &q;
            let parameter_denominator = Atom::num(4) * &a__ * &e__;
            let elliptic = rubi_elliptic_f(Atom::num(2) * (&q * x_).asin(), &b__ * &d__ / parameter_denominator);

            rubi_simp(&(elliptic / direct_denominator), x_)
        },
    ));
}

fn push_rules_rule_1560(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1560,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          Sqrt[(d+e*x^2)/d]*Sqrt[(a+b*x^2+c*x^4)/a]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4]) \\[Star]
            Int[1/(Sqrt[1+e/d*x^2]*Sqrt[1+b/a*x^2+c/a*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && Not[GtQ[a,0] && GtQ[d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * &d__ - &b__ * &e__, 0)
                && !(gtq!(a__, 0) && gtq!(d__, 0))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = quadratic.sqrt() * quartic.sqrt();
            let first_sqrt = (&quadratic / &d__).sqrt();
            let second_sqrt = (&quartic / &a__).sqrt();
            let recursive_integrand = Atom::num(1)
                / ((Atom::num(1) + &e__ * x_.pow(2) / &d__).sqrt()
                    * (Atom::num(1) + &b__ * x_.pow(2) / &a__ + &c__ * x_.pow(4) / &a__).sqrt());
            rubi_star(first_sqrt * second_sqrt / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1561(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1561,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4]) \\[Star]
            Int[1/(x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = quadratic.sqrt() * quartic.sqrt();
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &b__ / x_.pow(2) + &a__ / x_.pow(4);
            let recursive_denominator = x_.pow(3) * inverted_quadratic.sqrt() * inverted_quartic.sqrt();

            rubi_star(&recursive_denominator / denominator, rubi_rhs_int(&(Atom::num(1) / recursive_denominator), x_))
        },
    ));
}

fn push_rules_rule_1562(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1562,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+c*x^4]) \\[Star]
            Int[1/(x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]),x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + c__ * x_.pow(4)).sqrt()),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = quadratic.sqrt() * quartic.sqrt();
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &a__ / x_.pow(4);
            let recursive_denominator = x_.pow(3) * inverted_quadratic.sqrt() * inverted_quartic.sqrt();

            rubi_star(&recursive_denominator / denominator, rubi_rhs_int(&(Atom::num(1) / recursive_denominator), x_))
        },
    ));
}

fn push_rules_rule_1563(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1563,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Sqrt[a]/(2*Sqrt[d]*Rt[-e/d,2])*EllipticE[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && GtQ[a,0] && GtQ[d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * &d__ - &b__ * &e__, 0)
                && gtq!(a__, 0)
                && gtq!(d__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&e__ / &d__), 2);
            let direct_denominator = Atom::num(2) * d__.sqrt() * &q;
            let parameter_denominator = Atom::num(4) * &a__ * &e__;
            let elliptic = rubi_elliptic_e(Atom::num(2) * (&q * x_).asin(), &b__ * &d__ / parameter_denominator);

            rubi_simp(&(a__.sqrt() * elliptic / direct_denominator), x_)
        },
    ));
}

fn push_rules_rule_1564(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1564,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Sqrt[a+b*x^2+c*x^4]*Sqrt[(d+e*x^2)/d]/(Sqrt[d+e*x^2]*Sqrt[(a+b*x^2+c*x^4)/a]) \\[Star]
            Int[Sqrt[1+b/a*x^2+c/a*x^4]/Sqrt[1+e/d*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && Not[GtQ[a,0] && GtQ[d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * &d__ - &b__ * &e__, 0)
                && !(gtq!(a__, 0) && gtq!(d__, 0))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = quadratic.sqrt() * (&quartic / &a__).sqrt();
            let recursive_integrand = (Atom::num(1) + &b__ * x_.pow(2) / &a__ + &c__ * x_.pow(4) / &a__).sqrt()
                / (Atom::num(1) + &e__ * x_.pow(2) / &d__).sqrt();

            rubi_star(quartic.sqrt() * (&quadratic / &d__).sqrt() / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1565(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1565,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Sqrt[e+d/x^2]*Sqrt[a+b*x^2+c*x^4]/(x*Sqrt[d+e*x^2]*Sqrt[c+b/x^2+a/x^4]) \\[Star]
            Int[(x*Sqrt[c+b/x^2+a/x^4])/Sqrt[e+d/x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &b__ / x_.pow(2) + &a__ / x_.pow(4);
            let denominator = x_ * quadratic.sqrt() * inverted_quartic.sqrt();
            let recursive_integrand = x_ * inverted_quartic.sqrt() / inverted_quadratic.sqrt();

            rubi_star(inverted_quadratic.sqrt() * quartic.sqrt() / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1566(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1566,
        source: "Int[Sqrt[a_+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Sqrt[e+d/x^2]*Sqrt[a+c*x^4]/(x*Sqrt[d+e*x^2]*Sqrt[c+a/x^4]) \\[Star]
            Int[(x*Sqrt[c+a/x^4])/Sqrt[e+d/x^2],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + c__ * x_.pow(4)).sqrt() / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &a__ / x_.pow(4);
            let denominator = x_ * quadratic.sqrt() * inverted_quartic.sqrt();
            let recursive_integrand = x_ * inverted_quartic.sqrt() / inverted_quadratic.sqrt();

            rubi_star(inverted_quadratic.sqrt() * quartic.sqrt() / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1567(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1567,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b^2-4*a*c,0] && (IntegerQ[p] && IntegerQ[q] || IGtQ[p,0] || IGtQ[q,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ((integerq!(p_) && integerq!(q_)) || igtq!(p_, 0) || igtq!(q_, 0))
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)).pow(&q_) * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1568(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1568,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e,p,q},x] && (IntegerQ[p] && IntegerQ[q] || IGtQ[p,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && ((integerq!(p_) && integerq!(q_)) || igtq!(p_, 0))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1569(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1569,
        source: "Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+c*x^4)^p,(d/(d^2-e^2*x^4)-e*x^2/(d^2-e^2*x^4))^(-q),x],x] /;
        FreeQ[{a,c,d,e,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, p_],
        when: {
            freeq!([a__, c__, d__, e__, p_], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && iltq!(q_, 0)
        },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(4);
            let u = (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let v_expr = (&d__ / &denominator - &e__ * x_.pow(2) / denominator).pow(-&q_);
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1570(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1570,
        source: "Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [b__, c__, e__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, p_, q_], x_) },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1571(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1571,
        source: "Int[(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^q*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,d,e,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [c__, e__, p_, q_],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: { freeq!([a__, c__, d__, e__, p_, q_], x_) },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &c__ * x_.pow(4)).pow(&p_);
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt() / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt() / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (a__ + c__ * x_.pow(4)).sqrt() / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) * (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) / (a__ + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)) / (a__ + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    x_.pow(2) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}
