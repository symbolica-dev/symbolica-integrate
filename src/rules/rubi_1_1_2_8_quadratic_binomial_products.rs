use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_516(rules);
    push_rules_rule_517(rules);
    push_rules_rule_518(rules);
    push_rules_rule_519(rules);
    push_rules_rule_520(rules);
    push_rules_rule_521(rules);
    push_rules_rule_522(rules);
    push_rules_rule_523(rules);
    push_rules_rule_524(rules);
    push_rules_rule_525(rules);
    push_rules_rule_526(rules);
    push_rules_rule_527(rules);
    push_rules_rule_528(rules);
    push_rules_rule_529(rules);
    push_rules_rule_530(rules);
    push_rules_rule_531(rules);
    push_rules_rule_532(rules);
    push_rules_rule_533(rules);
    push_rules_rule_534(rules);
    push_rules_rule_535(rules);
    push_rules_rule_536(rules);
    push_rules_rule_537(rules);
    push_rules_rule_538(rules);
    push_rules_rule_539(rules);
    push_rules_rule_540(rules);
    push_rules_rule_541(rules);
    push_rules_rule_542(rules);
    push_rules_rule_543(rules);
    push_rules_rule_544(rules);
    push_rules_rule_545(rules);
    push_rules_rule_546(rules);
    push_rules_rule_547(rules);
    push_rules_rule_548(rules);
    push_rules_rule_549(rules);
    push_rules_rule_550(rules);
    push_rules_rule_551(rules);
    push_rules_rule_552(rules);
    push_rules_rule_553(rules);
    push_rules_rule_554(rules);
    push_rules_rule_556(rules);
    push_rules_rule_557(rules);
    push_rules_rule_558(rules);
    push_rules_rule_559(rules);
    push_rules_rule_560(rules);
    push_rules_rule_561(rules);
    push_rules_rule_562(rules);
    push_rules_rule_563(rules);
    push_rules_rule_564(rules);
    push_rules_rule_565(rules);
    push_rules_rule_566(rules);
    push_rules_rule_567(rules);
    push_rules_rule_568(rules);
    push_rules_rule_569(rules);
    push_rules_rule_570(rules);
    push_rules_rule_571(rules);
    push_rules_rule_572(rules);
    push_rules_rule_573(rules);
    push_rules_rule_574(rules);
    push_rules_rule_575(rules);
    push_rules_rule_576(rules);
    push_rules_rule_577(rules);
    push_rules_rule_578(rules);
    push_rules_rule_579(rules);
    push_rules_rule_580(rules);
    push_rules_rule_581(rules);
    push_rules_rule_582(rules);
    push_rules_rule_583(rules);
    push_rules_rule_584(rules);
    push_rules_rule_585(rules);
    push_rules_rule_586(rules);
    push_rules_rule_587(rules);
    push_rules_rule_588(rules);
    push_rules_rule_589(rules);
    push_rules_rule_590(rules);
    push_rules_rule_591(rules);
    push_rules_rule_592(rules);
    push_rules_rule_593(rules);
    push_rules_rule_594(rules);
    push_rules_rule_595(rules);
    push_rules_rule_596(rules);
    push_rules_rule_597(rules);
    push_rules_rule_598(rules);
    push_rules_rule_599(rules);
    push_rules_rule_600(rules);
    push_rules_rule_601(rules);
    push_rules_rule_602(rules);
    push_rules_rule_603(rules);
    push_rules_rule_604(rules);
    push_rules_rule_605(rules);
    push_rules_rule_606(rules);
    push_rules_rule_607(rules);
    push_rules_rule_608(rules);
    push_rules_rule_609(rules);
    push_rules_rule_610(rules);
    push_rules_rule_611(rules);
    push_rules_rule_612(rules);
    push_rules_rule_613(rules);
    push_rules_rule_614(rules);
    push_rules_rule_615(rules);
    push_rules_rule_616(rules);
    push_rules_rule_617(rules);
    push_rules_rule_618(rules);
    push_rules_rule_619(rules);
    push_rules_rule_620(rules);
    push_rules_rule_621(rules);
    push_rules_rule_622(rules);
    push_rules_rule_623(rules);
    push_rules_rule_624(rules);
    push_rules_rule_625(rules);
    push_rules_rule_626(rules);
    push_rules_rule_627(rules);
    push_rules_rule_628(rules);
    push_rules_rule_629(rules);
    push_rules_rule_630(rules);
    push_rules_rule_631(rules);
    push_rules_rule_632(rules);
    push_rules_rule_633(rules);
    push_rules_rule_634(rules);
    push_rules_rule_635(rules);
    push_rules_rule_636(rules);
    push_rules_rule_637(rules);
    push_rules_rule_638(rules);
}

fn push_rules_rule_516(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 516,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(e*x)^m*(c+d*x)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0] && Not[IntegerQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(p_)
                    || gtq!(a__, 0) && gtq!(c__, 0) && !integerq!(n_))
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_ + &p_)
                * (&a__ / &c__ + &b__ / &d__ * x_).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_517(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 517,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          2*e^m/d^(m+2*p+1) \\[Star] Subst[Int[x^(2*n+1)*(-c+x^2)^m*(b*c^2+a*d^2-2*b*c*x^2+b*x^4)^p,x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && ILtQ[m,0] && IntegerQ[n+1/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(m_, 0)
                && integerq!(&n_ + Atom::num(1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(Atom::num(2) * &n_ + 1)
                    * (-&c__ + sub_atom.pow(2)).pow(&m_)
                    * (&b__ * c__.pow(2) + &a__ * d__.pow(2)
                        - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2)
                        + &b__ * sub_atom.pow(4))
                    .pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            let coefficient = Atom::num(2) * e__.pow(&m_)
                / d__.pow(&m_ + Atom::num(2) * &p_ + 1);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_518(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 518,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          2/e^(n+2*p+1) \\[Star] Subst[Int[x^(2*m+1)*(e*c+d*x^2)^n*(a*e^2+b*x^4)^p,x],x,Sqrt[e*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && ILtQ[n,0] && IntegerQ[m+1/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && integerq!(&m_ + Atom::num(1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(Atom::num(2) * &m_ + 1)
                    * (&e__ * &c__ + &d__ * sub_atom.pow(2)).pow(&n_)
                    * (&a__ * e__.pow(2) + &b__ * sub_atom.pow(4)).pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, (&e__ * x_).sqrt());
            let coefficient = Atom::num(2)
                / e__.pow(&n_ + Atom::num(2) * &p_ + 1);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_519(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 519,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x^2)^p,c+d*x,x],R=PolynomialRemainder[(a+b*x^2)^p,c+d*x,x]},
          -R*(e*x)^(m+1)*(c+d*x)^(n+1)/(c*e*(n+1)) +
          1/(c*(n+1)) \\[Star] Int[(e*x)^m*(c+d*x)^(n+1)*ExpandToSum[c*(n+1)*Qx+R*(m+n+2),x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,0] && LtQ[n,-1] && Not[IntegerQ[m]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && ltq!(n_, -1)
                && !integerq!(m_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let capital_q = rubi_polynomial_quotient(&quadratic_power, &linear, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&quadratic_power, &linear, x_).rubi_rhs();
            let denominator = &c__ * &e__ * (&n_ + 1);
            let direct = -&capital_r
                * (&e__ * x_).pow(&m_ + 1)
                * linear.pow(&n_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&c__ * (&n_ + 1) * capital_q
                    + &capital_r * (&m_ + &n_ + 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * linear.pow(&n_ + 1) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_520(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 520,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x^2)^p,e*x,x],R=PolynomialRemainder[(a+b*x^2)^p,e*x,x]},
          R*(e*x)^(m+1)*(c+d*x)^(n+1)/((m+1)*(e*c)) +
          1/((m+1)*(e*c)) \\[Star] Int[(e*x)^(m+1)*(c+d*x)^n*ExpandToSum[(m+1)*(e*c)*Qx-d*R*(m+n+2),x],x]] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0] && LtQ[m,-1] && Not[IntegerQ[n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 0)
                && ltq!(m_, -1)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let capital_q = rubi_polynomial_quotient(&quadratic_power, &ex, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&quadratic_power, &ex, x_).rubi_rhs();
            let denominator = (&m_ + 1) * &e__ * &c__;
            let direct = &capital_r * ex.pow(&m_ + 1) * linear.pow(&n_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &((&m_ + 1) * &e__ * &c__ * capital_q
                    - &d__ * &capital_r * (&m_ + &n_ + 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * linear.pow(&n_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_521(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 521,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          b^p*(e*x)^(m+2*p)*(c+d*x)^(n+1)/(d*e^(2*p)*(m+n+2*p+1)) +
          1/(d*e^(2*p)*(m+n+2*p+1)) \\[Star] Int[(e*x)^m*(c+d*x)^n*
            ExpandToSum[d*(m+n+2*p+1)*(e^(2*p)*(a+b*x^2)^p-b^p*(e*x)^(2*p))-b^p*(e*c)*(m+2*p)*(e*x)^(2*p-1),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && NeQ[m+n+2*p+1,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 1, 0)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + &n_ + Atom::num(2) * &p_ + 1;
            let denominator = &d__ * e__.pow(Atom::num(2) * &p_) * &sum;
            let direct = b__.pow(&p_)
                * ex.pow(&m_ + Atom::num(2) * &p_)
                * linear.pow(&n_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&d__
                    * &sum
                    * (e__.pow(Atom::num(2) * &p_) * quadratic.pow(&p_)
                        - b__.pow(&p_) * ex.pow(Atom::num(2) * &p_))
                    - b__.pow(&p_)
                        * &e__
                        * &c__
                        * (&m_ + Atom::num(2) * &p_)
                        * ex.pow(Atom::num(2) * &p_ - 1)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * linear.pow(&n_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_522(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 522,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(c+d*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_523(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 523,
        source: "Int[x_^m_.*(c_+d_.*x_)/(a_+b_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[x^m*(c+d*x)/(a+b*x^2),x],x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) * (c__ + d__ * x_) / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && integerq!(m_) },
        rhs: {
            let integrand = x_.pow(&m_) * (&c__ + &d__ * x_)
                / (&a__ + &b__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_524(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 524,
        source: "Int[(c_+d_.*x_)^2/(x_*(a_+b_.*x_^2)),x_Symbol] :=
          c^2/a*Log[x] + 2*c*d \\[Star] Int[1/(a+b*x^2),x] - (b*c^2-a*d^2)/a \\[Star] Int[x/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(2) / (x_ * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / &quadratic), x_);
            let second = rubi_rhs_int(&(x_ / quadratic), x_);
            rubi_simp(&(c__.pow(2) / &a__ * x_.log()), x_)
                    + rubi_star(Atom::num(2) * &c__ * &d__, first)
                    - rubi_star((&b__ * c__.pow(2) - &a__ * d__.pow(2)) / &a__, second)
        },
    ));
}

fn push_rules_rule_525(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 525,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          d^n*x^(m+n-1)/(b*(m+n-1)) +
          1/b \\[Star] Int[x^m*ExpandToSum[b*(c+d*x)^n-b*d^n*x^n-a*d^n*x^(n-2),x]/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1] && IGtQ[m,-2] && NeQ[m+n-1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 1)
                && igtq!(m_, -2)
                && neq!(&m_ + &n_ - 1, 0)
        },
        rhs: {
            let denominator = &b__ * (&m_ + &n_ - 1);
            let direct = d__.pow(&n_) * x_.pow(&m_ + &n_ - 1) / &denominator;
            let payload = rubi_expand_to_sum(
                &(&b__ * (&c__ + &d__ * x_).pow(&n_)
                    - &b__ * d__.pow(&n_) * x_.pow(&n_)
                    - &a__ * d__.pow(&n_) * x_.pow(&n_ - 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * payload / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &b__, recursive)
        },
    ));
}

fn push_rules_rule_526(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 526,
        source: "Int[x_^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          With[{Qx=PolynomialQuotient[(c+d*x)^n,x,x], R=PolynomialRemainder[(c+d*x)^n,x,x]},
          R*x^(m+1)/(a*(m+1)) +
          1/a \\[Star] Int[x^(m+1)*ExpandToSum[a*Qx-b*R*x,x]/(a+b*x^2),x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1] && ILtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && igtq!(n_, 1) && iltq!(m_, -1)
        },
        rhs: {
            let linear_power = (&c__ + &d__ * x_).pow(&n_);
            let capital_q = rubi_polynomial_quotient(&linear_power, x_, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&linear_power, x_, x_).rubi_rhs();
            let direct = &capital_r * x_.pow(&m_ + 1) / (&a__ * (&m_ + 1));
            let payload = rubi_expand_to_sum(
                &(&a__ * capital_q - &b__ * &capital_r * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ + 1) * payload / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &a__, recursive)
        },
    ));
}

fn push_rules_rule_527(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 527,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_./(a_+b_.*x_^2)^(3/2),x_Symbol] :=
          -2^(n-1)*c^(m+n-2)*(c+d*x)/(b*d^(m-1)*Sqrt[a+b*x^2]) +
          1/(b*d^(m-2)) \\[Star] Int[(1/Sqrt[a+b*x^2])*ExpandToSum[(2^(n-1)*c^(m+n-1)-d^m*x^m*(c+d*x)^(n-1))/(c-d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && IGtQ[m,0] && EqQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__, m_, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && igtq!(m_, 0)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -Atom::num(2).pow(&n_ - 1)
                * c__.pow(&m_ + &n_ - 2)
                * &linear
                / (&b__ * d__.pow(&m_ - 1) * quadratic.sqrt());
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(&n_ - 1) * c__.pow(&m_ + &n_ - 1)
                    - d__.pow(&m_)
                        * x_.pow(&m_)
                        * linear.pow(&n_ - 1))
                    / (&c__ - &d__ * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(&(payload / quadratic.sqrt()), x_);
            let coefficient = Atom::num(1) / (&b__ * d__.pow(&m_ - 2));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_528(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 528,
        source: "Int[x_^m_*(c_+d_.*x_)^n_./(a_+b_.*x_^2)^(3/2),x_Symbol] :=
          -2^(n-1)*c^(m+n-2)*(c+d*x)/(b*d^(m-1)*Sqrt[a+b*x^2]) +
          c^2/a \\[Star] Int[x^m/Sqrt[a+b*x^2]*ExpandToSum[((c+d*x)^(n-1)-2^(n-1)*c^(m+n-1)*d^(-m)*x^(-m))/(c-d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && ILtQ[m,0] && EqQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && iltq!(m_, 0)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -Atom::num(2).pow(&n_ - 1)
                * c__.pow(&m_ + &n_ - 2)
                * &linear
                / (&b__ * d__.pow(&m_ - 1) * quadratic.sqrt());
            let payload = rubi_expand_to_sum(
                &((linear.pow(&n_ - 1)
                    - Atom::num(2).pow(&n_ - 1)
                        * c__.pow(&m_ + &n_ - 1)
                        * d__.pow(-&m_)
                        * x_.pow(-&m_))
                    / (&c__ - &d__ * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * payload / quadratic.sqrt()),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(c__.pow(2) / &a__, recursive)
        },
    ));
}

fn push_rules_rule_529(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 529,
        source: "Int[x_^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m,a*d+b*c*x,x], R=PolynomialRemainder[x^m,a*d+b*c*x,x]},
          -c*R*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*a*d*(p+1)) +
          c/(2*a*(p+1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1)*ExpandToSum[2*a*d*(p+1)*Qx+R*(n+2*p+2),x],x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && IGtQ[m,1] && LtQ[p,-1] && EqQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && igtq!(m_, 1)
                && ltq!(p_, -1)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let divisor = &a__ * &d__ + &b__ * &c__ * x_;
            let capital_q = rubi_polynomial_quotient(x_.pow(&m_), &divisor, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(x_.pow(&m_), &divisor, x_).rubi_rhs();
            let direct = -&c__
                * &capital_r
                * linear.pow(&n_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &d__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &d__ * (&p_ + 1) * capital_q
                    + &capital_r * (&n_ + Atom::num(2) * &p_ + 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient = &c__ / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_530(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 530,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m*(c+d*x)^n,a+b*x^2,x],
                e=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,0],
                f=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,1]},
          (a*f-b*e*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Qx+e*(2*p+3),x],x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && IGtQ[m,0] && LtQ[p,-1] && EqQ[n,1] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && igtq!(m_, 0)
                && ltq!(p_, -1)
                && eqq!(n_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let dividend = x_.pow(&m_) * (&c__ + &d__ * x_).pow(&n_);
            let capital_q = rubi_polynomial_quotient(&dividend, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&dividend, &quadratic, x_).rubi_rhs();
            let coeff_e = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let direct = (&a__ * &coeff_f - &b__ * &coeff_e * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + 1) * capital_q
                    + &coeff_e * (Atom::num(2) * &p_ + 3)),
                x_,
            );
            let recursive = rubi_rhs_int(&(quadratic.pow(&p_ + 1) * payload), x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_531(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 531,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m,a+b*x^2,x],
                e=Coeff[PolynomialRemainder[x^m,a+b*x^2,x],x,0],
                f=Coeff[PolynomialRemainder[x^m,a+b*x^2,x],x,1]},
          (c+d*x)^n*(a*f-b*e*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*b*(p +1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1)*
            ExpandToSum[2*a*b*(p+1)*(c+d*x)*Qx-a*d*f*n+b*c*e*(2*p+3)+b*d*e*(n+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && IGtQ[m,0] && LtQ[p,-1] && GtQ[n,1] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && igtq!(m_, 0)
                && ltq!(p_, -1)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let monomial = x_.pow(&m_);
            let capital_q = rubi_polynomial_quotient(&monomial, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&monomial, &quadratic, x_).rubi_rhs();
            let coeff_e = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let direct = linear.pow(&n_)
                * (&a__ * &coeff_f - &b__ * &coeff_e * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2)
                    * &a__
                    * &b__
                    * (&p_ + 1)
                    * &linear
                    * capital_q
                    - &a__ * &d__ * &coeff_f * &n_
                    + &b__ * &c__ * &coeff_e * (Atom::num(2) * &p_ + 3)
                    + &b__
                        * &d__
                        * &coeff_e
                        * (&n_ + Atom::num(2) * &p_ + 3)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient =
                Atom::num(1) / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_532(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 532,
        source: "Int[x_^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m*(c+d*x)^n,a+b*x^2,x],
                e=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,0],
                f=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,1]},
          (a*f-b*e*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[x^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Qx/x^m+e*(2*p+3)/x^m,x],x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && ILtQ[m,0] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && iltq!(m_, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let rational_denominator = x_.pow(-&m_);
            let (capital_q, remainder) = polynomial_quotient_remainder_rational_dividend(
                &linear.pow(&n_),
                &rational_denominator,
                &quadratic,
                x_,
            ).rubi_rhs();
            let coeff_e = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let direct = (&a__ * &coeff_f - &b__ * &coeff_e * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + 1) * capital_q / x_.pow(&m_)
                    + &coeff_e * (Atom::num(2) * &p_ + 3) / x_.pow(&m_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_533(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 533,
        source: "Int[x_^m_.*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*x^m*(a+b*x^2)^(p+1)/(b*(m+2*p+2)) -
          1/(b*(m+2*p+2)) \\[Star] Int[x^(m-1)*(a+b*x^2)^p*Simp[a*d*m-b*c*(m+2*p+2)*x,x],x] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[m,0] && GtQ[p,-1] && IntegerQ[2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(m_, 0)
                && gtq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&m_ + Atom::num(2) * &p_ + 2);
            let direct = &d__ * x_.pow(&m_) * quadratic.pow(&p_ + 1)
                / &denominator;
            let simplified = rubi_simp(
                &(&a__ * &d__ * &m_
                    - &b__
                        * &c__
                        * (&m_ + Atom::num(2) * &p_ + 2)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ - 1) * quadratic.pow(&p_) * simplified),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_534(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 534,
        source: "Int[x_^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -c*x^(m+1)*(a+b*x^2)^(p+1)/(2*a*(p+1)) + d \\[Star] Int[x^(m+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,m,p},x] && ILtQ[m,0] && GtQ[p,-1] && EqQ[m+2*p+3,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && iltq!(m_, 0)
                && gtq!(p_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -&c__ * x_.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * (&p_ + 1));
            let recursive = rubi_rhs_int(&(x_.pow(&m_ + 1) * quadratic.pow(&p_)), x_);
            rubi_simp(&(direct), x_) + rubi_star(d__, recursive)
        },
    ));
}

fn push_rules_rule_535(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 535,
        source: "Int[(c_+d_.*x_)*(a_+b_.*x_^2)^p_/x_,x_Symbol] :=
          (c*(2*p+1)+2*d*p*x)*(a+b*x^2)^p/(2*p*(2*p+1)) +
          a/(2*p+1) \\[Star] Int[(c*(2*p+1)+2*d*p*x)*(a+b*x^2)^(p-1)/x,x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow(p_) / x_,
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let numerator = &c__ * (Atom::num(2) * &p_ + 1)
                + Atom::num(2) * &d__ * &p_ * x_;
            let direct = &numerator * quadratic.pow(&p_)
                / (Atom::num(2) * &p_ * (Atom::num(2) * &p_ + 1));
            let recursive = rubi_rhs_int(
                &(numerator * quadratic.pow(&p_ - 1) / x_),
                x_,
            );
            let coefficient = &a__ / (Atom::num(2) * &p_ + 1);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_536(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 536,
        source: "Int[(c_+d_.*x_)*(a_+b_.*x_^2)^p_/x_^2,x_Symbol] :=
          -(2*c*p-d*x)*(a+b*x^2)^p/(2*p*x) + Int[(a*d+2*b*c*p*x)*(a+b*x^2)^(p-1)/x,x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow(p_) / x_.pow(2),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -(&c__ * Atom::num(2) * &p_ - &d__ * x_)
                * quadratic.pow(&p_)
                / (Atom::num(2) * &p_ * x_);
            let recursive = rubi_rhs_int(
                &((&a__ * &d__ + Atom::num(2) * &b__ * &c__ * &p_ * x_)
                    * quadratic.pow(&p_ - 1)
                    / x_),
                x_,
            );
            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_537(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 537,
        source: "Int[x_^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          x^(m+1)*(c*(m+2)+d*(m+1)*x)*(a+b*x^2)^p/((m+1)*(m+2)) -
          2*b*p/((m+1)*(m+2)) \\[Star] Int[x^(m+2)*(c*(m+2)+d*(m+1)*x)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,-2] && GtQ[p,0] && Not[ILtQ[m+2*p+3,0]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(m_, -2)
                && gtq!(p_, 0)
                && !iltq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear = &c__ * (&m_ + 2) + &d__ * (&m_ + 1) * x_;
            let denominator = (&m_ + 1) * (&m_ + 2);
            let direct = x_.pow(&m_ + 1) * &linear * quadratic.pow(&p_)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ + 2) * linear * quadratic.pow(&p_ - 1)),
                x_,
            );
            let coefficient = Atom::num(2) * &b__ * &p_ / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_538(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 538,
        source: "Int[(c_+d_.*x_)/(x_*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          c \\[Star] Int[1/(x*Sqrt[a+b*x^2]),x] + d \\[Star] Int[1/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_) / (x_ * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let root = (&a__ + &b__ * x_.pow(2)).sqrt();
            let first = rubi_rhs_int(&(Atom::num(1) / (x_ * &root)), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / root), x_);
            rubi_star(c__, first) + rubi_star(d__, second)
        },
    ));
}

fn push_rules_rule_539(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 539,
        source: "Int[x_^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*x^(m+1)*(a+b*x^2)^(p+1)/(a*(m+1)) +
          1/(a*(m+1))\\[Star]Int[x^(m+1)*(a+b*x^2)^p*(a*d*(m+1)-b*c*(m+2*p+3)*x),x] /;
        FreeQ[{a,b,c,d,p},x] && ILtQ[m,-1] && GtQ[p,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && iltq!(m_, -1)
                && gtq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &a__ * (&m_ + 1);
            let direct = &c__ * x_.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ + 1)
                    * quadratic.pow(&p_)
                    * (&a__ * &d__ * (&m_ + 1)
                        - &b__
                            * &c__
                            * (&m_ + Atom::num(2) * &p_ + 3)
                            * x_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_540(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 540,
        source: "Int[x_^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(c+d*x)^n,x,x], R=PolynomialRemainder[(c+d*x)^n,x,x]},
          R*x^(m+1)*(a+b*x^2)^(p+1)/(a*(m+1)) +
          1/(a*(m+1)) \\[Star] Int[x^(m+1)*(a+b*x^2)^p*ExpandToSum[a*(m+1)*Qx-b*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[n,1] && ILtQ[m,-1] && GtQ[p,-1] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(n_, 1)
                && iltq!(m_, -1)
                && gtq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear_power = (&c__ + &d__ * x_).pow(&n_);
            let capital_q = rubi_polynomial_quotient(&linear_power, x_, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&linear_power, x_, x_).rubi_rhs();
            let denominator = &a__ * (&m_ + 1);
            let direct = &capital_r * x_.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&a__ * (&m_ + 1) * capital_q
                    - &b__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + 3)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ + 1) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_541(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 541,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d^n*x^(m+n-1)*(a+b*x^2)^(p+1)/(b*(m+n+2*p+1)) +
          1/(b*(m+n+2*p+1)) \\[Star] Int[x^m*(a+b*x^2)^p*
            ExpandToSum[b*(m+n+2*p+1)*(c+d*x)^n-b*d^n*(m+n+2*p+1)*x^n-a*d^n*(m+n-1)*x^(n-2),x],x] /;
        FreeQ[{a,b,c,d,m,p},x] && IGtQ[n,1] && IGtQ[m,-2] && GtQ[p,-1] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && igtq!(n_, 1)
                && igtq!(m_, -2)
                && gtq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + &n_ + Atom::num(2) * &p_ + 1;
            let denominator = &b__ * &sum;
            let direct = d__.pow(&n_)
                * x_.pow(&m_ + &n_ - 1)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&b__ * &sum * (&c__ + &d__ * x_).pow(&n_)
                    - &b__ * d__.pow(&n_) * &sum * x_.pow(&n_)
                    - &a__
                        * d__.pow(&n_)
                        * (&m_ + &n_ - 1)
                        * x_.pow(&n_ - 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_542(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 542,
        source: "Int[x_^m_.*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c \\[Star] Int[x^m*(a+b*x^2)^p,x] + d \\[Star] Int[x^(m+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && IntegerQ[m] && Not[IntegerQ[2*p]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && integerq!(m_)
                && !integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(x_.pow(&m_) * quadratic.pow(&p_)), x_);
            let second = rubi_rhs_int(&(x_.pow(&m_ + 1) * quadratic.pow(&p_)), x_);
            rubi_star(c__, first) + rubi_star(d__, second)
        },
    ));
}

fn push_rules_rule_543(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 543,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Module[{k},
          Int[x^m*Sum[Binomial[n,2*k]*c^(n-2*k)*d^(2*k)*x^(2*k),{k,0,n/2}]*(a+b*x^2)^p,x] +
          Int[x^(m+1)*Sum[Binomial[n,2*k+1]*c^(n-2*k-1)*d^(2*k+1)*x^(2*k),{k,0,(n-1)/2}]*(a+b*x^2)^p,x]] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[n,1] && IntegerQ[m] && Not[IntegerQ[2*p]] && Not[EqQ[m,1] && EqQ[b*c^2+a*d^2,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(n_, 1)
                && integerq!(m_)
                && !integerq!(Atom::num(2) * &p_)
                && !(eqq!(m_, 1)
                    && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0))
        },
        rhs: {
            let n = integer_i64(&n_).rubi_rhs();
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let mut even_sum = Atom::num(0);
            for k in 0..=n / 2 {
                let two_k = 2 * k;
                even_sum += rubi_binomial_coefficient(n, two_k).rubi_rhs()
                    * c__.pow(n - two_k)
                    * d__.pow(two_k)
                    * x_.pow(two_k);
            }
            let mut odd_sum = Atom::num(0);
            for k in 0..=(n - 1) / 2 {
                let two_k = 2 * k;
                odd_sum += rubi_binomial_coefficient(n, two_k + 1).rubi_rhs()
                    * c__.pow(n - two_k - 1)
                    * d__.pow(two_k + 1)
                    * x_.pow(two_k);
            }
            let first = rubi_rhs_int(
                &(x_.pow(&m_) * even_sum * &quadratic_power),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_.pow(&m_ + 1) * odd_sum * quadratic_power),
                x_,
            );
            first + second
        },
    ));
}

fn push_rules_rule_544(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 544,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^m*(a*d-b*c*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) -
          e*d*m/(2*b*(p+1))*Int[(e*x)^(m-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[Simplify[m+2*p+3],0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + 3)), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = ex.pow(&m_)
                * (&a__ * &d__ - &b__ * &c__ * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let recursive = rubi_rhs_int(&(ex.pow(&m_ - 1) * quadratic.pow(&p_ + 1)), x_);
            rubi_simp(&(direct), x_)
                    - rubi_simp(&(&e__ * &d__ * &m_ / (Atom::num(2) * &b__ * (&p_ + 1))
                        * recursive), x_)
        },
    ));
}

fn push_rules_rule_545(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 545,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -c*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(2*a*e*(p+1)) +
          d/e \\[Star] Int[(e*x)^(m+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[Simplify[m+2*p+3],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + 3)), 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -&c__ * ex.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &e__ * (&p_ + 1));
            let recursive = rubi_rhs_int(&(ex.pow(&m_ + 1) * quadratic.pow(&p_)), x_);
            rubi_simp(&(direct), x_) + rubi_star(&d__ / &e__, recursive)
        },
    ));
}

fn push_rules_rule_546(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 546,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(c*(m+2)+d*(m+1)*x)*(a+b*x^2)^p/(e*(m+1)*(m+2)) -
          2*b*p/(e^2*(m+1)*(m+2)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^(p-1)*(c*(m+2)+d*(m+1)*x),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[p,0] && LtQ[m,-2] && Not[ILtQ[m+2*p+3,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -2)
                && !iltq!(&m_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear = &c__ * (&m_ + 2) + &d__ * (&m_ + 1) * x_;
            let denominator = &e__ * (&m_ + 1) * (&m_ + 2);
            let direct = ex.pow(&m_ + 1) * &linear * quadratic.pow(&p_) / &denominator;
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 2) * quadratic.pow(&p_ - 1) * linear),
                x_,
            );
            let coefficient = Atom::num(2) * &b__ * &p_
                / (e__.pow(2) * (&m_ + 1) * (&m_ + 2));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_547(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 547,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(c*(m+2*p+2)+d*(m+1)*x)*(a+b*x^2)^p/(e*(m+1)*(m+2*p+2)) +
          2*p/(e*(m+1)*(m+2*p+2)) \\[Star] Int[(e*x)^(m+1)*(a*d*(m+1)-b*c*(m+2*p+2)*x)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[p,0] && LtQ[m,-1] && Not[ILtQ[m+2*p+1,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && !iltq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + Atom::num(2) * &p_ + 2;
            let linear = &c__ * &sum + &d__ * (&m_ + 1) * x_;
            let denominator = &e__ * (&m_ + 1) * &sum;
            let direct = ex.pow(&m_ + 1) * &linear * quadratic.pow(&p_) / &denominator;
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1)
                    * (&a__ * &d__ * (&m_ + 1)
                        - &b__ * &c__ * &sum * x_)
                    * quadratic.pow(&p_ - 1)),
                x_,
            );
            let coefficient = Atom::num(2) * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_548(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 548,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(c*(m+2*p+2)+d*(m+2*p+1)*x)*(a+b*x^2)^p/(e*(m+2*p+1)*(m+2*p+2)) +
          2*a*p/((m+2*p+1)*(m+2*p+2)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p-1)*(c*(m+2*p+2)+d*(m+2*p+1)*x),x] /;
        FreeQ[{a,b,c,d,e,m},x] && GtQ[p,0] && (IntegerQ[p] || Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,0]) && Not[ILtQ[m+2*p,0]] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && gtq!(p_, 0)
                && (integerq!(p_)
                    || !rationalq!(m_)
                    || geq!(m_, -1) && ltq!(m_, 0))
                && !iltq!(&m_ + Atom::num(2) * &p_, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first_sum = &m_ + Atom::num(2) * &p_ + 1;
            let second_sum = &m_ + Atom::num(2) * &p_ + 2;
            let linear = &c__ * &second_sum + &d__ * &first_sum * x_;
            let denominator = &e__ * &first_sum * &second_sum;
            let direct = ex.pow(&m_ + 1) * &linear * quadratic.pow(&p_) / &denominator;
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * quadratic.pow(&p_ - 1) * linear),
                x_,
            );
            let coefficient = Atom::num(2) * &a__ * &p_ / (&first_sum * &second_sum);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_549(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 549,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          e*(e*x)^(m-1)*(c+d*x)*(a+b*x^2)^(p+1)/(2*b*(p+1)) -
          e^2/(2*b*(p+1)) \\[Star] Int[(e*x)^(m-2)*(c*(m-1)+d*m*x)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[p,-1] && GtQ[m,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && ltq!(p_, -1) && gtq!(m_, 1)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &e__ * ex.pow(&m_ - 1) * linear * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &b__ * (&p_ + 1));
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ - 2)
                    * (&c__ * (&m_ - 1) + &d__ * &m_ * x_)
                    * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = e__.pow(2) / (Atom::num(2) * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_550(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 550,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^m*(a*d-b*c*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) -
          e/(2*a*b*(p+1)) \\[Star] Int[(e*x)^(m-1)*(a*d*m-b*c*(m+2*p+3)*x)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[p,-1] && LtQ[0,m,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(p_, -1)
                && ltq!(0, m_, 1)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = ex.pow(&m_)
                * (&a__ * &d__ - &b__ * &c__ * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ - 1)
                    * (&a__ * &d__ * &m_
                        - &b__
                            * &c__
                            * (&m_ + Atom::num(2) * &p_ + 3)
                            * x_)
                    * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = &e__ / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_551(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 551,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(e*x)^(m+1)*(c+d*x)*(a+b*x^2)^(p+1)/(2*a*e*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(e*x)^m*(c*(m+2*p+3)+d*(m+2*p+4)*x)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && LtQ[p,-1] && LtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && ltq!(p_, -1) && ltq!(m_, 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -ex.pow(&m_ + 1) * linear * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &e__ * (&p_ + 1));
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_)
                    * (&c__ * (&m_ + Atom::num(2) * &p_ + 3)
                        + &d__
                            * (&m_ + Atom::num(2) * &p_ + 4)
                            * x_)
                    * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_552(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 552,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(e*x)^m*(a+b*x^2)^(p+1)/(b*(m+2*p+2)) -
          e/(b*(m+2*p+2)) \\[Star] Int[(e*x)^(m-1)*(a+b*x^2)^p*Simp[a*d*m-b*c*(m+2*p+2)*x,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && GtQ[m,0] && NeQ[m+2*p+2,0] && (IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && gtq!(m_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 2, 0)
                && (integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + Atom::num(2) * &p_ + 2;
            let direct = &d__ * ex.pow(&m_) * quadratic.pow(&p_ + 1) / (&b__ * &sum);
            let simplified = rubi_simp(
                &(&a__ * &d__ * &m_ - &b__ * &c__ * &sum * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ - 1) * quadratic.pow(&p_) * simplified),
                x_,
            );
            let coefficient = &e__ / (&b__ * &sum);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_553(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 553,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*e*(m+1)) +
          1/(a*e*(m+1))\\[Star]Int[(e*x)^(m+1)*(a+b*x^2)^p*(a*d*(m+1)-b*c*(m+2*p+3)*x),x] /;
        FreeQ[{a,b,c,d,e,p},x] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, p_], x_) && ltq!(m_, -1) },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &a__ * &e__ * (&m_ + 1);
            let direct = &c__ * ex.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1)
                    * quadratic.pow(&p_)
                    * (&a__ * &d__ * (&m_ + 1)
                        - &b__
                            * &c__
                            * (&m_ + Atom::num(2) * &p_ + 3)
                            * x_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_554(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 554,
        source: "Int[(c_+d_.*x_)/(Sqrt[e_.*x_]*(a_+b_.*x_^2)),x_Symbol] :=
          2 \\[Star] Subst[Int[(e*c+d*x^2)/(a*e^2+b*x^4),x],x,Sqrt[e*x]] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (c__ + d__ * x_)
            / ((e__ * x_).sqrt() * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((&e__ * &c__ + &d__ * sub_atom.pow(2))
                    / (&a__ * e__.pow(2) + &b__ * sub_atom.pow(4))),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, (&e__ * x_).sqrt());
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_556(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 556,
        source: "Int[(c_+d_.*x_)/(Sqrt[e_*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          Sqrt[x]/Sqrt[e*x] \\[Star] Int[(c+d*x)/(Sqrt[x]*Sqrt[a+b*x^2]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_)
            / ((e__ * x_).sqrt() * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let recursive = rubi_rhs_int(
                &((&c__ + &d__ * x_)
                    / (x_.sqrt() * (&a__ + &b__ * x_.pow(2)).sqrt())),
                x_,
            );
            let multiplier = x_.sqrt() / (&e__ * x_).sqrt();
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_557(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 557,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c \\[Star] Int[(e*x)^m*(a+b*x^2)^p,x] + d/e \\[Star] Int[(e*x)^(m+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, p_], x_) },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(ex.pow(&m_) * quadratic.pow(&p_)), x_);
            let second = rubi_rhs_int(&(ex.pow(&m_ + 1) * quadratic.pow(&p_)), x_);
            rubi_star(c__, first) + rubi_star(&d__ / &e__, second)
        },
    ));
}

fn push_rules_rule_558(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 558,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(c+d*x)^n,a+b*x^2,x],
                f=Coeff[PolynomialRemainder[(c+d*x)^n,a+b*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[(c+d*x)^n,a+b*x^2,x],x,1]},
          -(e*x)^(m+1)*(f+g*x)*(a+b*x^2)^(p+1)/(2*a*e*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Qx+f*(m+2*p+3)+g*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1] && Not[IntegerQ[m]] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, n_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 1)
                && !integerq!(m_)
                && ltq!(p_, -1)
        },
        rhs: {
            let ex = &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear_power = (&c__ + &d__ * x_).pow(&n_);
            let capital_q = rubi_polynomial_quotient(&linear_power, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&linear_power, &quadratic, x_).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_g = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let direct = -ex.pow(&m_ + 1)
                * (&coeff_f + &coeff_g * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &e__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + 1) * capital_q
                    + &coeff_f * (&m_ + Atom::num(2) * &p_ + 3)
                    + &coeff_g
                        * (&m_ + Atom::num(2) * &p_ + 4)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_559(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 559,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d^n*(e*x)^(m+n-1)*(a+b*x^2)^(p+1)/(b*e^(n-1)*(m+n+2*p+1)) +
          1/(b*(m+n+2*p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^p*
            ExpandToSum[b*(m+n+2*p+1)*(c+d*x)^n-b*d^n*(m+n+2*p+1)*x^n-a*d^n*(m+n-1)*x^(n-2),x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && IGtQ[n,1] && Not[IntegerQ[m]] && NeQ[m+n+2*p+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && igtq!(n_, 1)
                && !integerq!(m_)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + &n_ + Atom::num(2) * &p_ + 1;
            let direct = d__.pow(&n_)
                * ex.pow(&m_ + &n_ - 1)
                * quadratic.pow(&p_ + 1)
                / (&b__ * e__.pow(&n_ - 1) * &sum);
            let payload = rubi_expand_to_sum(
                &(&b__ * &sum * linear.pow(&n_)
                    - &b__ * d__.pow(&n_) * &sum * x_.pow(&n_)
                    - &a__
                        * d__.pow(&n_)
                        * (&m_ + &n_ - 1)
                        * x_.pow(&n_ - 2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            let coefficient = Atom::num(1) / (&b__ * &sum);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_560(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 560,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Module[{k},
          Int[(e*x)^m*Sum[Binomial[n,2*k]*c^(n-2*k)*d^(2*k)*x^(2*k),{k,0,n/2}]*(a+b*x^2)^p,x] +
          1/e \\[Star] Int[(e*x)^(m+1)*Sum[Binomial[n,2*k+1]*c^(n-2*k-1)*d^(2*k+1)*x^(2*k),{k,0,(n-1)/2}]*(a+b*x^2)^p,x]] /;
        FreeQ[{a,b,c,d,e,p},x] && IGtQ[n,1] && Not[IntegerQ[m]] && EqQ[m+n+2*p+1,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && igtq!(n_, 1)
                && !integerq!(m_)
                && eqq!(&m_ + &n_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let n = integer_i64(&n_).rubi_rhs();
            let ex = &e__ * x_;
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let mut even_sum = Atom::num(0);
            for k in 0..=n / 2 {
                let two_k = 2 * k;
                even_sum += rubi_binomial_coefficient(n, two_k).rubi_rhs()
                    * c__.pow(n - two_k)
                    * d__.pow(two_k)
                    * x_.pow(two_k);
            }
            let mut odd_sum = Atom::num(0);
            for k in 0..=(n - 1) / 2 {
                let two_k = 2 * k;
                odd_sum += rubi_binomial_coefficient(n, two_k + 1).rubi_rhs()
                    * c__.pow(n - two_k - 1)
                    * d__.pow(two_k + 1)
                    * x_.pow(two_k);
            }
            let first = rubi_rhs_int(&(ex.pow(&m_) * even_sum * &quadratic_power), x_);
            let second = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * odd_sum * quadratic_power),
                x_,
            );
            first + rubi_star(Atom::num(1) / &e__, second)
        },
    ));
}

fn push_rules_rule_561(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 561,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k/d \\[Star] Subst[Int[x^(k*(n+1)-1)*(-c/d+x^k/d)^m*Simp[(b*c^2+a*d^2)/d^2-2*b*c*x^k/d^2+b*x^(2*k)/d^2,x]^p,x],x,(c+d*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,m,p},x] && FractionQ[n] && IntegerQ[p] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && fractionq!(n_)
                && integerq!(p_)
                && integerq!(m_)
        },
        rhs: {
            let k = denominator!(n_);
            if k == 0 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let k_atom = Atom::num(k);
            let simplified = rubi_simp(
                &((&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                    - Atom::num(2) * &b__ * &c__ * sub_atom.pow(&k_atom) / d__.pow(2)
                    + &b__ * sub_atom.pow(Atom::num(2) * &k_atom) / d__.pow(2)),
                sub,
            );
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&k_atom * (&n_ + 1) - 1)
                    * (-&c__ / &d__ + sub_atom.pow(&k_atom) / &d__).pow(&m_)
                    * simplified.pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).pow(Atom::num(1) / &k_atom),
            );
            rubi_star(&k_atom / &d__, substituted)
        },
    ));
}

fn push_rules_rule_562(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 562,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^(2*n)/a^n \\[Star] Int[x^m*(a+b*x^2)^(n+p)/(c-d*x)^n,x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[m,0] && ILtQ[n,0] && IGtQ[n+p+1/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && igtq!(&n_ + &p_ + Atom::num(1) / 2, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&n_ + &p_)
                    / (&c__ - &d__ * x_).pow(&n_)),
                x_,
            );
            let coefficient = c__.pow(Atom::num(2) * &n_) / a__.pow(&n_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_563(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 563,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(-c)^(m-n-2)*d^(2*n-m+3)*Sqrt[a+b*x^2]/(2^(n+1)*b^(n+2)*(c+d*x)) -
          d^(2*n-m+2)/b^(n+1) \\[Star] Int[1/Sqrt[a+b*x^2]*ExpandToSum[(2^(-n-1)*(-c)^(m-n-1)-d^m*x^m*(-c+d*x)^(-n-1))/(c+d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[m,0] && ILtQ[n,0] && EqQ[n+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && eqq!(&n_ + &p_, -Atom::num(3) / 2)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear = &c__ + &d__ * x_;
            let direct = -(-&c__).pow(&m_ - &n_ - 2)
                * d__.pow(Atom::num(2) * &n_ - &m_ + 3)
                * quadratic.sqrt()
                / (Atom::num(2).pow(&n_ + 1) * b__.pow(&n_ + 2) * &linear);
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(-&n_ - 1) * (-&c__).pow(&m_ - &n_ - 1)
                    - d__.pow(&m_)
                        * x_.pow(&m_)
                        * (-&c__ + &d__ * x_).pow(-&n_ - 1))
                    / linear),
                x_,
            );
            let recursive = rubi_rhs_int(&(payload / quadratic.sqrt()), x_);
            let coefficient =
                d__.pow(Atom::num(2) * &n_ - &m_ + 2) / b__.pow(&n_ + 1);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_564(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 564,
        source: "Int[x_^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(-c)^(m-n-2)*d^(2*n-m+3)*Sqrt[a+b*x^2]/(2^(n+1)*b^(n+2)*(c+d*x)) -
          d^(2*n+2)/b^(n+1) \\[Star] Int[x^m/Sqrt[a+b*x^2]*ExpandToSum[(2^(-n-1)*(-c)^(m-n-1)*d^(-m)*x^(-m)-(-c+d*x)^(-n-1))/(c+d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[m,0] && ILtQ[n,0] && EqQ[n+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(m_, 0)
                && iltq!(n_, 0)
                && eqq!(&n_ + &p_, -Atom::num(3) / 2)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let linear = &c__ + &d__ * x_;
            let direct = -(-&c__).pow(&m_ - &n_ - 2)
                * d__.pow(Atom::num(2) * &n_ - &m_ + 3)
                * quadratic.sqrt()
                / (Atom::num(2).pow(&n_ + 1) * b__.pow(&n_ + 2) * &linear);
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(-&n_ - 1)
                    * (-&c__).pow(&m_ - &n_ - 1)
                    * d__.pow(-&m_)
                    * x_.pow(-&m_)
                    - (-&c__ + &d__ * x_).pow(-&n_ - 1))
                    / linear),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * payload / quadratic.sqrt()),
                x_,
            );
            let coefficient = d__.pow(Atom::num(2) * &n_ + 2) / b__.pow(&n_ + 1);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_565(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 565,
        source: "Int[x_*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          a*(a+b*x^2)^p/(2*b*c*p) + b/d \\[Star] Int[x^2*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_ * (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &a__ * quadratic.pow(&p_) / (Atom::num(2) * &b__ * &c__ * &p_);
            let recursive = rubi_rhs_int(
                &(x_.pow(2) * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&b__ / &d__, recursive)
        },
    ));
}

fn push_rules_rule_566(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 566,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          Int[x^m*(a/c+b*x/d)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let integrand = x_.pow(&m_)
                * (&a__ / &c__ + &b__ * x_ / &d__)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ - 1);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_567(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 567,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          c*x^m*(a+b*x^2)^(p+1)/(2*a*d*p*(c+d*x)) -
          m/(2*d*p) \\[Star] Int[x^(m-1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[m,1] && LtQ[p,-1] && EqQ[m+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(m_, 1)
                && ltq!(p_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &c__ * x_.pow(&m_) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &d__ * &p_ * (&c__ + &d__ * x_));
            let recursive = rubi_rhs_int(&(x_.pow(&m_ - 1) * quadratic.pow(&p_)), x_);
            let coefficient = &m_ / (Atom::num(2) * &d__ * &p_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_568(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 568,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          x^(m-1)*(a+b*x^2)^(p+1)/(2*b*p*(c+d*x)) +
          1/(2*d^2*p) \\[Star] Int[x^(m-2)*(a+b*x^2)^p*(c*(m-1)-d*m*x),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[m,1] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(m_, 1)
                && ltq!(p_, -1)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = x_.pow(&m_ - 1) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &b__ * &p_ * (&c__ + &d__ * x_));
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ - 2)
                    * quadratic.pow(&p_)
                    * (&c__ * (&m_ - 1) - &d__ * &m_ * x_)),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * d__.pow(2) * &p_);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_569(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 569,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          -x^(m+1)*(a+b*x^2)^(p+1)/(2*a*p*(c+d*x)) +
          1/(2*c^2*p) \\[Star] Int[x^m*(a+b*x^2)^p*(c*(m+2*p+1)-d*(m+2*p+2)*x),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[m+2*p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(&m_ + Atom::num(2) * &p_, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = Atom::num(-1) * x_.pow(&m_ + 1) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &p_ * (&c__ + &d__ * x_));
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * quadratic.pow(&p_)
                    * (&c__ * (&m_ + Atom::num(2) * &p_ + 1)
                        - &d__
                            * (&m_ + Atom::num(2) * &p_ + 2)
                            * x_)),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * c__.pow(2) * &p_);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_570(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 570,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^(2*n)/a^n \\[Star] Int[(e*x)^m*(a+b*x^2)^(n+p)/(c-d*x)^n,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[n,-1] && Not[IGtQ[m,0] && ILtQ[m+n,0] && Not[GtQ[p,1]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(n_, -1)
                && !(igtq!(m_, 0) && iltq!(&m_ + &n_, 0) && !gtq!(p_, 1))
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&n_ + &p_)
                    / (&c__ - &d__ * x_).pow(&n_)),
                x_,
            );
            let coefficient = c__.pow(Atom::num(2) * &n_) / a__.pow(&n_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_571(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 571,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^n*(a+b*x^2)^(p+1)/(2*b*(n+p+1)) +
          n/(2*d*(n+p+1)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && (LtQ[n,-1] && Not[IGtQ[n+p+1,0]] || LtQ[n,0] && LtQ[p,-1] || EqQ[n+2*p+2,0]) && NeQ[n+p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && ((ltq!(n_, -1) && !igtq!(&n_ + &p_ + 1, 0))
                    || (ltq!(n_, 0) && ltq!(p_, -1))
                    || eqq!(&n_ + Atom::num(2) * &p_ + 2, 0))
                && neq!(&n_ + &p_ + 1, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &b__ * (&n_ + &p_ + 1);
            let direct = linear.pow(&n_) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive = rubi_rhs_int(&(linear.pow(&n_ + 1) * quadratic.pow(&p_)), x_);
            let coefficient = &n_ / (Atom::num(2) * &d__ * (&n_ + &p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_572(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 572,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^n*(a+b*x^2)^(p+1)/(b*(n+2*p+2)) +
          c*n/(d*(n+2*p+2)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && NeQ[n+2*p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && neq!(&n_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&n_ + Atom::num(2) * &p_ + 2);
            let direct = linear.pow(&n_) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive = rubi_rhs_int(&(linear.pow(&n_) * quadratic.pow(&p_)), x_);
            let coefficient = &c__ * &n_ / (&d__ * (&n_ + Atom::num(2) * &p_ + 2));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_573(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 573,
        source: "Int[Sqrt[c_+d_.*x_]/(x_*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -2*c \\[Star] Subst[Int[1/(a-c*x^2),x],x,Sqrt[a+b*x^2]/Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&a__ - &c__ * sub_atom.pow(2))),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&a__ + &b__ * x_.pow(2)).sqrt()
                    / (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(-Atom::num(2) * &c__, substituted)
        },
    ));
}

fn push_rules_rule_574(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 574,
        source: "Int[(e_.*x_)^n_*(c_+d_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d^2*(e*x)^(n+1)*(c+d*x)^(m-2)*(a+b*x^2)^(p+1)/(b*e*(n+p+2)) +
          c*(2*n+p+3)/(n+p+2) \\[Star] Int[(e*x)^n*(c+d*x)^(m-1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[b*c^2+a*d^2,0] && EqQ[m+p-1,0] && Not[LtQ[n,-1]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (e__ * x_).pow(n_)
            * (c__ + d__ * x_).pow(m_)
            * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&m_ + &p_ - 1, 0)
                && !ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = d__.pow(2)
                * ex.pow(&n_ + 1)
                * linear.pow(&m_ - 2)
                * quadratic.pow(&p_ + 1)
                / (&b__ * &e__ * (&n_ + &p_ + 2));
            let recursive = rubi_rhs_int(
                &(ex.pow(&n_) * linear.pow(&m_ - 1) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &c__ * (Atom::num(2) * &n_ + &p_ + 3) / (&n_ + &p_ + 2);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_575(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 575,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(c+d*x)^n*(a+b*x^2)^p/(e*(m+1)) +
          b*n/(d*e*(m+1)) \\[Star] Int[(e*x)^(m+1)*(c+d*x)^(n+1)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0] && GtQ[p,0] && LtQ[m,-1] && Not[IntegerQ[m+p] && LeQ[m+p+2,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && !(integerq!(&m_ + &p_) && leq!(&m_ + &p_ + 2, 0))
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = ex.pow(&m_ + 1) * linear.pow(&n_) * quadratic.pow(&p_)
                / (&e__ * (&m_ + 1));
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * linear.pow(&n_ + 1) * quadratic.pow(&p_ - 1)),
                x_,
            );
            let coefficient = &b__ * &n_ / (&d__ * &e__ * (&m_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_576(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 576,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(e*x)^(m+1)*(c+d*x)^n*(a+b*x^2)^p/(e*(n-m-1)) -
          b*c*n/(d^2*(n-m-1)) \\[Star] Int[(e*x)^m*(c+d*x)^(n+1)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0] && GtQ[p,0] && NeQ[m-n+1,0] &&
          Not[IGtQ[m,0]] && Not[IntegerQ[m+p] && LtQ[m+p+2,0]] && RationalQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ - &n_ + 1, 0)
                && !igtq!(m_, 0)
                && !(integerq!(&m_ + &p_) && ltq!(&m_ + &p_ + 2, 0))
                && rationalq!(m_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &n_ - &m_ - 1;
            let direct = -ex.pow(&m_ + 1) * linear.pow(&n_) * quadratic.pow(&p_)
                / (&e__ * &denominator);
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * linear.pow(&n_ + 1) * quadratic.pow(&p_ - 1)),
                x_,
            );
            let coefficient = &b__ * &c__ * &n_ / (d__.pow(2) * &denominator);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_577(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 577,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(e*x)^m*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(p+1)) -
          d*e*m/(b*(p+1)) \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&p_ + 1);
            let direct = &d__ * ex.pow(&m_) * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ - 1) * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = &d__ * &e__ * &m_ / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_578(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 578,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -c*(e*x)^(m+1)*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(a*e*(p+1)) +
          c*(m-n+2)/(a*(p+1)) \\[Star] Int[(e*x)^m*(c+d*x)^(n-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0] && LtQ[p,-1] && RationalQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
                && ltq!(p_, -1)
                && rationalq!(m_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &a__ * (&p_ + 1);
            let direct = -&c__ * ex.pow(&m_ + 1) * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)
                / (&e__ * &denominator);
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_) * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = &c__ * (&m_ - &n_ + 2) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_579(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 579,
        source: "Int[(c_+d_.*x_)^n_*(e_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -d^2*(e*x)^(m+1)*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*c*e*(m+1)) -
          d*(n-m-2)/(c*e*(m+1)) \\[Star] Int[(e*x)^(m+1)*(c+d*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0] && LtQ[m,-1] && (IntegerQ[2*p] || IntegerQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(n_)
            * (e__ * x_).pow(m_)
            * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
                && ltq!(m_, -1)
                && (integerq!(Atom::num(2) * &p_) || integerq!(m_))
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &c__ * &e__ * (&m_ + 1);
            let direct = -d__.pow(2)
                * ex.pow(&m_ + 1)
                * linear.pow(&n_ - 1)
                * quadratic.pow(&p_ + 1)
                / (&b__ * &denominator);
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * linear.pow(&n_) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &d__ * (&n_ - &m_ - 2) / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_580(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 580,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -d^2*(e*x)^(m+1)*(c+d*x)^(n-2)*(a+b*x^2)^(p+1)/(b*e*(m+1)) +
          d*(2*m+p+3)/(e*(m+1)) \\[Star] Int[(e*x)^(m+1)*(c+d*x)^(n-1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p-1,0] && LtQ[m,-1] && IntegerQ[p+1/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_ - 1, 0)
                && ltq!(m_, -1)
                && integerq!(&p_ + Atom::num(1) / 2)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &e__ * (&m_ + 1);
            let direct = -d__.pow(2)
                * ex.pow(&m_ + 1)
                * linear.pow(&n_ - 2)
                * quadratic.pow(&p_ + 1)
                / (&b__ * &denominator);
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * linear.pow(&n_ - 1) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &d__ * (Atom::num(2) * &m_ + &p_ + 3) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_581(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 581,
        source: "Int[x_^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(m+n-1)*(a+b*x^2)^(p+1)/(b*d^(m-1)*(m+n+2*p+1)) +
          1/(d^m*(m+n+2*p+1)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^p*
            ExpandToSum[(d^m*(m+n+2*p+1)*x^m-(m+n+2*p+1)*(c+d*x)^m+c*(c+d*x)^(m-2)*(c*(m+n-1)+c*(m+n+2*p+1)+2*d*(m+n+p)*x)),x],x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[m,1] && NeQ[m+n+2*p+1,0] && (IntegerQ[2*p] || ILtQ[m+n,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(m_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 1, 0)
                && (integerq!(Atom::num(2) * &p_) || iltq!(&m_ + &n_, 0))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + &n_ + Atom::num(2) * &p_ + 1;
            let direct = linear.pow(&m_ + &n_ - 1) * quadratic.pow(&p_ + 1)
                / (&b__ * d__.pow(&m_ - 1) * &sum);
            let expanded = rubi_expand_to_sum(
                &(d__.pow(&m_) * &sum * x_.pow(&m_)
                    - &sum * linear.pow(&m_)
                    + &c__
                        * linear.pow(&m_ - 2)
                        * (&c__ * (&m_ + &n_ - 1)
                            + &c__ * &sum
                            + Atom::num(2)
                                * &d__
                                * (&m_ + &n_ + &p_)
                                * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_) * expanded),
                x_,
            );
            let coefficient = Atom::num(1) / (d__.pow(&m_) * &sum);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_582(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 582,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(c+d*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c^2+a*d^2,0] && IntegerQ[2*p] && IntegerQ[m] && ILtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && integerq!(Atom::num(2) * &p_)
                && integerq!(m_)
                && iltq!(n_, 0)
        },
        rhs: {
            let integrand = x_.pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_583(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 583,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^(2*n)/a^n \\[Star] Int[(e*x)^m*(a+b*x^2)^(n+p)/(c-d*x)^n,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[n,0] (* && Not[IGtQ[m,0] && ILtQ[m+n,0] && Not[GtQ[p,1]]] *)",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&n_ + &p_)
                    / (&c__ - &d__ * x_).pow(&n_)),
                x_,
            );
            let coefficient = c__.pow(Atom::num(2) * &n_) / a__.pow(&n_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_584(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 584,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[(e*x)^m*(c+d*x)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[b*c^2+a*d^2,0] && GtQ[a,0] && GtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(a__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_ + &p_)
                * (&a__ / &c__ + &b__ * x_ / &d__).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_585(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 585,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^p*c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n] \\[Star] Int[(e*x)^m*(1-d*x/c)^p*(1+d*x/c)^(n+p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[b*c^2+a*d^2,0] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(a__, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let frac_n = rubi_frac_part(&n_);
            let coefficient = a__.pow(&p_)
                * c__.pow(rubi_int_part(&n_))
                * linear.pow(&frac_n)
                / (Atom::num(1) + &d__ * x_ / &c__).pow(&frac_n);
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (Atom::num(1) - &d__ * x_ / &c__).pow(&p_)
                    * (Atom::num(1) + &d__ * x_ / &c__).pow(&n_ + &p_)),
                x_,
            );
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_586(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 586,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^FracPart[p]/((c+d*x)^FracPart[p]*(a/c+(b*x)/d)^FracPart[p]) \\[Star] Int[(e*x)^m*(c+d*x)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let reduced_linear = &a__ / &c__ + &b__ * x_ / &d__;
            let frac_p = rubi_frac_part(&p_);
            let coefficient = quadratic.pow(&frac_p)
                / (linear.pow(&frac_p) * reduced_linear.pow(&frac_p));
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * linear.pow(&n_ + &p_)
                    * reduced_linear.pow(&p_)),
                x_,
            );
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_587(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 587,
        source: "Int[x_./((c_+d_.*x_)*(a_+b_.*x_^2)),x_Symbol] :=
          -c*d/(b*c^2+a*d^2) \\[Star] Int[1/(c+d*x),x] + 1/(b*c^2+a*d^2) \\[Star] Int[(a*d+b*c*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c^2+a*d^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: x_ / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__, x_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&c__ + &d__ * x_)),
                x_,
            );
            let second = rubi_rhs_int(
                &((&a__ * &d__ + &b__ * &c__ * x_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_star(-&c__ * &d__ / &discriminant, first)
                    + rubi_star(Atom::num(1) / discriminant, second)
        },
    ));
}

fn push_rules_rule_588(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 588,
        source: "Int[x_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/(2*(p+1)*(b*c^2+a*d^2)) +
          a*d/(b*c^2+a*d^2) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[Simplify[n+2*p+3],0] && NeQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, x_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(
                    rubi_simplify(&(&n_ + Atom::num(2) * &p_ + 3)),
                    0
                )
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = &c__ * linear.pow(&n_ + 1) * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * (&p_ + 1) * &discriminant);
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &a__ * &d__ / discriminant;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_589(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 589,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c+d*x)^(n+1)*(a+b*x^2)^p*(c*(a*d^2+b*c^2*(2*p+1))-d*(a*d^2*(n+1)+b*c^2*(n-2*p+1))*x)/
            (d^2*(n+1)*(n+2)*(b*c^2+a*d^2)) +
          b*p/(d^2*(n+1)*(n+2)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^(n+2)*(a+b*x^2)^(p-1)*
            Simp[2*a*c*d*(n+2)-(2*a*d^2*(n+1)-2*b*c^2*(2*p+1))*x,x],x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0] && LtQ[n,-2] && LtQ[n+2*p,0] && Not[ILtQ[n+2*p+3,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(p_, 0)
                && ltq!(n_, -2)
                && ltq!(&n_ + Atom::num(2) * &p_, 0)
                && !iltq!(&n_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let numerator = &c__
                * (&a__ * d__.pow(2) + &b__ * c__.pow(2) * (Atom::num(2) * &p_ + 1))
                - &d__
                    * (&a__ * d__.pow(2) * (&n_ + 1)
                        + &b__ * c__.pow(2) * (&n_ - Atom::num(2) * &p_ + 1))
                    * x_;
            let denominator = d__.pow(2) * (&n_ + 1) * (&n_ + 2) * &discriminant;
            let direct = -linear.pow(&n_ + 1) * quadratic.pow(&p_) * numerator
                / &denominator;
            let payload = rubi_simp(
                &(Atom::num(2) * &a__ * &c__ * &d__ * (&n_ + 2)
                    - (Atom::num(2) * &a__ * d__.pow(2) * (&n_ + 1)
                        - Atom::num(2)
                            * &b__
                            * c__.pow(2)
                            * (Atom::num(2) * &p_ + 1))
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ + 2) * quadratic.pow(&p_ - 1) * payload),
                x_,
            );
            let coefficient = &b__ * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_590(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 590,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c+d*x)^(n+1)*(a+b*x^2)^p*(c*(2*p+1)-d*(n+1)*x)/(d^2*(n+1)*(n+2*p+2)) +
          2*p/(d^2*(n+1)*(n+2*p+2)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^(p-1)*(a*d*(n+1)+b*c*(2*p+1)*x),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0] && LtQ[n,-1] && Not[ILtQ[n+2*p+1,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(p_, 0)
                && ltq!(n_, -1)
                && !iltq!(&n_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = d__.pow(2) * (&n_ + 1) * (&n_ + Atom::num(2) * &p_ + 2);
            let direct = -linear.pow(&n_ + 1)
                * quadratic.pow(&p_)
                * (&c__ * (Atom::num(2) * &p_ + 1) - &d__ * (&n_ + 1) * x_)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ + 1)
                    * quadratic.pow(&p_ - 1)
                    * (&a__ * &d__ * (&n_ + 1)
                        + &b__ * &c__ * (Atom::num(2) * &p_ + 1) * x_)),
                x_,
            );
            let coefficient = Atom::num(2) * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_591(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 591,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c+d*x)^(n+1)*(a+b*x^2)^p*(c*(2*p+1)-d*(n+2*p+1)*x)/(d^2*(n+2*p+1)*(n+2*p+2)) +
          2*p/(d^2*(n+2*p+1)*(n+2*p+2)) \\[Star]
            Int[(c+d*x)^n*(a+b*x^2)^(p-1)*Simp[a*c*d*n+(b*c^2*(2*p+1)+a*d^2*(n+2*p+1))*x,x],x] /;
        FreeQ[{a,b,c,d,n},x] && GtQ[p,0] && LeQ[-1,n,0] && Not[ILtQ[n+2*p,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && gtq!(p_, 0)
                && leq!(-1, n_, 0)
                && !iltq!(&n_ + Atom::num(2) * &p_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first_sum = &n_ + Atom::num(2) * &p_ + 1;
            let second_sum = &n_ + Atom::num(2) * &p_ + 2;
            let denominator = d__.pow(2) * &first_sum * &second_sum;
            let direct = -linear.pow(&n_ + 1)
                * quadratic.pow(&p_)
                * (&c__ * (Atom::num(2) * &p_ + 1) - &d__ * &first_sum * x_)
                / &denominator;
            let payload = rubi_simp(
                &(&a__ * &c__ * &d__ * &n_
                    + (&b__ * c__.pow(2) * (Atom::num(2) * &p_ + 1)
                        + &a__ * d__.pow(2) * &first_sum)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_ - 1) * payload),
                x_,
            );
            let coefficient = Atom::num(2) * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_592(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 592,
        source: "Int[x_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^n*(a+b*x^2)^(p+1)/(2*b*(p+1)) - d*n/(2*b*(p+1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && LtQ[p,-1] && GtQ[n,0] && (IntegerQ[n] || IntegerQ[p] || IntegersQ[2*n,2*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
                && (integerq!(n_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_]))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &b__ * (&p_ + 1);
            let direct = linear.pow(&n_) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)),
                x_,
            );
            let coefficient = &d__ * &n_ / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_593(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 593,
        source: "Int[x_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(c-d*x)*(a+b*x^2)^(p+1)/(2*(p+1)*(b*c^2+a*d^2)) -
          d/(2*(p+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^(p+1)*(c*n-d*(n+2*p+4)*x),x] /;
        FreeQ[{a,b,c,d,n},x] && LtQ[p,-1] && NeQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && ltq!(p_, -1)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let denominator = Atom::num(2) * (&p_ + 1) * &discriminant;
            let direct = linear.pow(&n_ + 1)
                * (&c__ - &d__ * x_)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_)
                    * quadratic.pow(&p_ + 1)
                    * (&c__ * &n_ - &d__ * (&n_ + Atom::num(2) * &p_ + 4) * x_)),
                x_,
            );
            let coefficient = &d__ / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_594(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 594,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -c*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/((n+1)*(b*c^2+a*d^2)) +
          1/((n+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p*(a*d*(n+1)+b*c*(n+2*p+3)*x),x] /;
        FreeQ[{a,b,c,d,p},x] && LtQ[n,-1] && NeQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && ltq!(n_, -1)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let denominator = (&n_ + 1) * &discriminant;
            let direct = -&c__ * linear.pow(&n_ + 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ + 1)
                    * quadratic.pow(&p_)
                    * (&a__ * &d__ * (&n_ + 1)
                        + &b__ * &c__ * (&n_ + Atom::num(2) * &p_ + 3) * x_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_595(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 595,
        source: "Int[x_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          (c+d*x)^n/(b*n) - 1/b \\[Star] Int[(c+d*x)^(n-1)*(a*d-b*c*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_ * (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && gtq!(n_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = linear.pow(&n_) / (&b__ * &n_);
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ - 1)
                    * (&a__ * &d__ - &b__ * &c__ * x_)
                    / quadratic),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / b__, recursive)
        },
    ));
}

fn push_rules_rule_596(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 596,
        source: "Int[x_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^n*(a+b*x^2)^(p+1)/(b*(n+2*p+2)) -
          n/(b*(n+2*p+2)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^p*(a*d-b*c*x),x] /;
        FreeQ[{a,b,c,d,p},x] && GtQ[n,0] && NeQ[n+2*p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && gtq!(n_, 0)
                && neq!(&n_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&n_ + Atom::num(2) * &p_ + 2);
            let direct = linear.pow(&n_) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ - 1)
                    * quadratic.pow(&p_)
                    * (&a__ * &d__ - &b__ * &c__ * x_)),
                x_,
            );
            let coefficient = &n_ / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_597(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 597,
        source: "Int[x_/((c_+d_.*x_)*(a_+b_.*x_^2)^(3/4)),x_Symbol] :=
          With[{q=Rt[-a,4]},
          c/(2*d^2*q^3)*ArcTan[c*q*(a+b*x^2)^(1/4)/(q^2*(c+d*x)-c*Sqrt[a+b*x^2])] +
          c/(2*d^2*q^3)*ArcTanh[c*q*(a+b*x^2)^(1/4)/(q^2*(c+d*x)+c*Sqrt[a+b*x^2])]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+2*a*d^2,0] && NegQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(2) * &a__ * d__.pow(2), 0)
                && negq!(a__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__), 4);
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let numerator = &c__ * &q * quadratic.pow((1, 4));
            let first = (&numerator
                / (q.pow(2) * &linear - &c__ * quadratic.sqrt()))
                .atan();
            let second = (numerator
                / (q.pow(2) * linear + &c__ * quadratic.sqrt()))
                .atanh();
            let coefficient = &c__ / (Atom::num(2) * d__.pow(2) * q.pow(3));
            rubi_simp(&(&coefficient * first), x_) + rubi_simp(&(coefficient * second), x_)
        },
    ));
}

fn push_rules_rule_598(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 598,
        source: "Int[x_/((c_+d_.*x_)*(a_+b_.*x_^2)^(3/4)),x_Symbol] :=
          (-a-b*x^2)^(3/4)/(a+b*x^2)^(3/4) \\[Star] Int[x/((c+d*x)*(-a-b*x^2)^(3/4)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+2*a*d^2,0] && PosQ[a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(2) * &a__ * d__.pow(2), 0)
                && posq!(a__)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let negative_quadratic = -&a__ - &b__ * x_.pow(2);
            let recursive = rubi_rhs_int(
                &(x_
                    / ((&c__ + &d__ * x_) * negative_quadratic.pow((3, 4)))),
                x_,
            );
            let coefficient = negative_quadratic.pow((3, 4)) / quadratic.pow((3, 4));
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_599(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, capital_a__, capital_b__, x_);
    rules.push(rubi_rule!(
        order: 599,
        source: "Int[(A_.+B_.*x_)/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -2/d^2 \\[Star] Subst[Int[(B*c-A*d-B*x^2)/Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2],x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,A,B},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, capital_a__, capital_b__, x_],
        optional: [b__, d__, capital_a__, capital_b__],
        x_free: [a__, b__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__], x_)
                && posq!(&b__ / &a__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let radicand = (&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2);
            let primitive = rubi_rhs_int(
                &((&capital_b__ * &c__
                    - &capital_a__ * &d__
                    - &capital_b__ * sub_atom.pow(2))
                    / radicand.sqrt()),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(-Atom::num(2) / d__.pow(2), substituted)
        },
    ));
}

fn push_rules_rule_600(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, capital_a__, capital_b__, x_);
    rules.push(rubi_rule!(
        order: 600,
        source: "Int[(A_.+B_.*x_)/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          B/d \\[Star] Int[Sqrt[c+d*x]/Sqrt[a+b*x^2],x] - (B*c-A*d)/d \\[Star] Int[1/(Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] /;
        FreeQ[{a,b,c,d,A,B},x] && NegQ[b/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, capital_a__, capital_b__, x_],
        optional: [b__, d__, capital_a__, capital_b__],
        x_free: [a__, b__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__], x_)
                && negq!(&b__ / &a__)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(linear.sqrt() / quadratic.sqrt()), x_);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&capital_b__ / &d__, first)
                    - rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / &d__, second)
        },
    ));
}

fn push_rules_rule_601(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 601,
        source: "Int[x_^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m*(c+d*x)^n,a+b*x^2,x],
                e=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,0],
                f=Coeff[PolynomialRemainder[x^m*(c+d*x)^n,a+b*x^2,x],x,1]},
          (a*f-b*e*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*(c+d*x)^(-n)*Qx+e*(2*p+3)*(c+d*x)^(-n),x],x]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,1] && LtQ[p,-1] && ILtQ[n,0] && NeQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(m_, 1)
                && ltq!(p_, -1)
                && iltq!(n_, 0)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let (capital_q, remainder) = polynomial_quotient_remainder_rational_dividend(
                x_.pow(&m_),
                &linear.pow(-&n_),
                &quadratic,
                x_,
            ).rubi_rhs();
            let coeff_e = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let direct = (&a__ * &coeff_f - &b__ * &coeff_e * x_)
                * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + 1) * capital_q / linear.pow(&n_)
                    + &coeff_e * (Atom::num(2) * &p_ + 3) / linear.pow(&n_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_602(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 602,
        source: "Int[x_^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m,a+b*x^2,x],
                e=Coeff[PolynomialRemainder[x^m,a+b*x^2,x],x,0],
                f=Coeff[PolynomialRemainder[x^m,a+b*x^2,x],x,1]},
          -(c+d*x)^(n+1)*(a+b*x^2)^(p+1)*(a*(d*e-c*f)+(b*c*e+a*d*f)*x)/(2*a*(p+1)*(b*c^2+a*d^2)) +
          1/(2*a*(p+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^(p+1)*
            ExpandToSum[2*a*(p+1)*(b*c^2+a*d^2)*Qx+e*(b*c^2*(2*p+3)+a*d^2*(n+2*p+3))-a*c*d*f*n+d*(b*c*e+a*d*f)*(n+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,1] && LtQ[p,-1] && NeQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, n_],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 1)
                && ltq!(p_, -1)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let capital_q = rubi_polynomial_quotient(x_.pow(&m_), &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(x_.pow(&m_), &quadratic, x_).rubi_rhs();
            let coeff_e = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let coeff_f = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = -linear.pow(&n_ + 1)
                * quadratic.pow(&p_ + 1)
                * (&a__ * (&d__ * &coeff_e - &c__ * &coeff_f)
                    + (&b__ * &c__ * &coeff_e + &a__ * &d__ * &coeff_f) * x_)
                / (Atom::num(2) * &a__ * (&p_ + 1) * &discriminant);
            let payload = rubi_expand_to_sum(
                &(Atom::num(2)
                    * &a__
                    * (&p_ + 1)
                    * &discriminant
                    * capital_q
                    + &coeff_e
                        * (&b__ * c__.pow(2) * (Atom::num(2) * &p_ + 3)
                            + &a__ * d__.pow(2) * (&n_ + Atom::num(2) * &p_ + 3))
                    - &a__ * &c__ * &d__ * &coeff_f * &n_
                    + &d__
                        * (&b__ * &c__ * &coeff_e + &a__ * &d__ * &coeff_f)
                        * (&n_ + Atom::num(2) * &p_ + 4)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_ + 1) * payload),
                x_,
            );
            let coefficient =
                Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1) * discriminant);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_603(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 603,
        source: "Int[x_^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m,c+d*x,x], R=PolynomialRemainder[x^m,c+d*x,x]},
          d*R*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/((n+1)*(b*c^2+a*d^2)) +
          1/((n+1)*(b*c^2+a*d^2)) \\[Star]
            Int[(c+d*x)^(n+1)*(a+b*x^2)^p*ExpandToSum[(n+1)*(b*c^2+a*d^2)*Qx+b*c*R*(n+1)-b*d*R*(n+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[m,1] && LtQ[n,-1] && NeQ[b*c^2+a*d^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(m_, 1)
                && ltq!(n_, -1)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let capital_q = rubi_polynomial_quotient(x_.pow(&m_), &linear, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(x_.pow(&m_), &linear, x_).rubi_rhs();
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let denominator = (&n_ + 1) * &discriminant;
            let direct = &d__
                * &capital_r
                * linear.pow(&n_ + 1)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &((&n_ + 1) * &discriminant * capital_q
                    + &b__ * &c__ * &capital_r * (&n_ + 1)
                    - &b__
                        * &d__
                        * &capital_r
                        * (&n_ + Atom::num(2) * &p_ + 3)
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_604(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 604,
        source: "Int[x_^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(m+n-1)*(a+b*x^2)^(p+1)/(b*d^(m-1)*(m+n+2*p+1)) +
          1/(b*d^m*(m+n+2*p+1)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^p*
            ExpandToSum[(b*d^m*(m+n+2*p+1)*x^m-b*(m+n+2*p+1)*(c+d*x)^m-(c+d*x)^(m-2)*(a*d^2*(m+n-1)-b*c^2*(m+n+2*p+1)-2*b*c*d*(m+n+p)*x)),x],x] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,1] && NeQ[m+n+2*p+1,0] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && igtq!(m_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let sum = &m_ + &n_ + Atom::num(2) * &p_ + 1;
            let direct = linear.pow(&m_ + &n_ - 1) * quadratic.pow(&p_ + 1)
                / (&b__ * d__.pow(&m_ - 1) * &sum);
            let payload = rubi_expand_to_sum(
                &(&b__ * d__.pow(&m_) * &sum * x_.pow(&m_)
                    - &b__ * &sum * linear.pow(&m_)
                    - linear.pow(&m_ - 2)
                        * (&a__ * d__.pow(2) * (&m_ + &n_ - 1)
                            - &b__ * c__.pow(2) * &sum
                            - Atom::num(2)
                                * &b__
                                * &c__
                                * &d__
                                * (&m_ + &n_ + &p_)
                                * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_) * payload),
                x_,
            );
            let coefficient = Atom::num(1) / (&b__ * d__.pow(&m_) * &sum);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_605(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 605,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          1/d \\[Star] Int[x^(m-1)*(a+b*x^2)^p,x] - c/d \\[Star] Int[x^(m-1)*(a+b*x^2)^p/(c+d*x),x] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[m,0] && LtQ[-1,p,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(m_, 0)
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let first = rubi_rhs_int(&(x_.pow(&m_ - 1) * &quadratic_power), x_);
            let second = rubi_rhs_int(
                &(x_.pow(&m_ - 1) * quadratic_power / (&c__ + &d__ * x_)),
                x_,
            );
            rubi_star(Atom::num(1) / &d__, first)
                    - rubi_star(&c__ / &d__, second)
        },
    ));
}

fn push_rules_rule_606(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 606,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_/x_,x_Symbol] :=
          a/c \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^(p-1)/x,x] -
          1/c \\[Star] Int[(c+d*x)^n*(a*d-b*c*x)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0] && ILtQ[n,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_) / x_,
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && gtq!(p_, 0) && iltq!(n_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_ - 1) / x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&n_)
                    * (&a__ * &d__ - &b__ * &c__ * x_)
                    * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_star(&a__ / &c__, first)
                    - rubi_star(Atom::num(1) / c__, second)
        },
    ));
}

fn push_rules_rule_607(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 607,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          e*d/b \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n-2)*(2*c+d*x),x] -
          e/b \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n-2)*Simp[2*a*c*d-(b*c^2-a*d^2)*x,x]/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[n,1] && GtQ[m,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(n_, 1)
                && gtq!(m_, 0)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(ex.pow(&m_ - 1)
                    * linear.pow(&n_ - 2)
                    * (Atom::num(2) * &c__ + &d__ * x_)),
                x_,
            );
            let payload = rubi_simp(
                &(Atom::num(2) * &a__ * &c__ * &d__
                    - (&b__ * c__.pow(2) - &a__ * d__.pow(2)) * x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(ex.pow(&m_ - 1) * linear.pow(&n_ - 2) * payload / quadratic),
                x_,
            );
            rubi_star(&e__ * &d__ / &b__, first)
                    - rubi_star(&e__ / &b__, second)
        },
    ));
}

fn push_rules_rule_608(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 608,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          e^2/b \\[Star] Int[(e*x)^(m-2)*(c+d*x)^n,x] - a*e^2/b \\[Star] Int[(e*x)^(m-2)*(c+d*x)^n/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[0,n,1] && GtQ[m,1] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(0, n_, 1)
                && gtq!(m_, 1)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear_power = (&c__ + &d__ * x_).pow(&n_);
            let first = rubi_rhs_int(&(ex.pow(&m_ - 2) * &linear_power), x_);
            let second = rubi_rhs_int(
                &(ex.pow(&m_ - 2)
                    * linear_power
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_star(e__.pow(2) / &b__, first)
                    - rubi_star(&a__ * e__.pow(2) / &b__, second)
        },
    ));
}

fn push_rules_rule_609(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 609,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          d*e/b \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n-1),x] -
          e/b \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n-1)*(a*d-b*c*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[0,n,1] && LtQ[0,m,1] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(0, n_, 1)
                && ltq!(0, m_, 1)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let common = ex.pow(&m_ - 1) * linear.pow(&n_ - 1);
            let first = rubi_rhs_int(&common, x_);
            let second = rubi_rhs_int(
                &(common * (&a__ * &d__ - &b__ * &c__ * x_) / quadratic),
                x_,
            );
            rubi_star(&d__ * &e__ / &b__, first)
                    - rubi_star(&e__ / &b__, second)
        },
    ));
}

fn push_rules_rule_610(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 610,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          e^(m+1/2) \\[Star] Int[ExpandIntegrand[1/(Sqrt[e*x]*Sqrt[c+d*x]),x^(m+1/2)*(c+d*x)^(n+1/2)/(a+b*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n+1/2,0] && ILtQ[m-1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(&n_ + Atom::num(1) / 2, 0)
                && iltq!(&m_ - Atom::num(1) / 2, 0)
        },
        rhs: {
            let first = Atom::num(1)
                / ((&e__ * x_).sqrt() * (&c__ + &d__ * x_).sqrt());
            let second = x_.pow(&m_ + Atom::num(1) / 2)
                * (&c__ + &d__ * x_).pow(&n_ + Atom::num(1) / 2)
                / (&a__ + &b__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            rubi_star(e__.pow(&m_ + Atom::num(1) / 2), recursive)
        },
    ));
}

fn push_rules_rule_611(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 611,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          c/a \\[Star] Int[(e*x)^m*(c+d*x)^(n-1),x] +
          1/(a*e) \\[Star] Int[((e*x)^(m+1)*(c+d*x)^(n-1)*(a*d-b*c*x))/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[n,0] && LtQ[m,-1] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let first = rubi_rhs_int(&(ex.pow(&m_) * linear.pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(
                &(ex.pow(&m_ + 1)
                    * linear.pow(&n_ - 1)
                    * (&a__ * &d__ - &b__ * &c__ * x_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_star(&c__ / &a__, first)
                    + rubi_star(Atom::num(1) / (&a__ * &e__), second)
        },
    ));
}

fn push_rules_rule_612(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 612,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          -e*c*d/(b*c^2+a*d^2) \\[Star] Int[(e*x)^(m-1)*(c+d*x)^n,x] +
          e/(b*c^2+a*d^2) \\[Star] Int[(e*x)^(m-1)*(c+d*x)^(n+1)*(a*d+b*c*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[n,-1] && GtQ[m,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(n_, -1)
                && gtq!(m_, 0)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let discriminant = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let first = rubi_rhs_int(&(ex.pow(&m_ - 1) * linear.pow(&n_)), x_);
            let second = rubi_rhs_int(
                &(ex.pow(&m_ - 1)
                    * linear.pow(&n_ + 1)
                    * (&a__ * &d__ + &b__ * &c__ * x_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_star(-&e__ * &c__ * &d__ / &discriminant, first)
                    + rubi_star(&e__ / discriminant, second)
        },
    ));
}

fn push_rules_rule_613(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 613,
        source: "Int[Sqrt[e_.*x_]/(Sqrt[c_+d_.*x_]*(a_+b_.*x_^2)),x_Symbol] :=
          e/(2*b) \\[Star] Int[1/(Sqrt[e*x]*Sqrt[c+d*x]*(Rt[-a/b,2]+x)),x] -
          e/(2*b) \\[Star] Int[1/(Sqrt[e*x]*Sqrt[c+d*x]*(Rt[-a/b,2]-x)),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ * x_).sqrt()
            / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let common = (&e__ * x_).sqrt() * (&c__ + &d__ * x_).sqrt();
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&common * (&root + x_))),
                x_,
            );
            let second = rubi_rhs_int(
                &(Atom::num(1) / (common * (root - x_))),
                x_,
            );
            let coefficient = &e__ / (Atom::num(2) * &b__);
            rubi_star(&coefficient, first)
                    - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_614(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 614,
        source: "Int[(e_.*x_)^m_/(Sqrt[c_+d_.*x_]*(a_+b_.*x_^2)),x_Symbol] :=
          e^(m+1/2) \\[Star] Int[ExpandIntegrand[1/(Sqrt[e*x]*Sqrt[c+d*x]),x^(m+1/2)/(a+b*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m-1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(&m_ - Atom::num(1) / 2, 0)
        },
        rhs: {
            let first = Atom::num(1)
                / ((&e__ * x_).sqrt() * (&c__ + &d__ * x_).sqrt());
            let second = x_.pow(&m_ + Atom::num(1) / 2)
                / (&a__ + &b__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            rubi_star(e__.pow(&m_ + Atom::num(1) / 2), recursive)
        },
    ));
}

fn push_rules_rule_615(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 615,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(c+d*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && ILtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && iltq!(p_, 0)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_616(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 616,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(c+d*x^k/e)^n*(a+b*x^(2*k)/e^2)^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,p},x] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&k * (&m_ + 1) - 1)
                    * (&c__ + &d__ * sub_atom.pow(&k) / &e__).pow(&n_)
                    * (&a__ + &b__ * sub_atom.pow(Atom::num(2) * &k) / e__.pow(2))
                        .pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&e__ * x_).pow(Atom::num(1) / &k),
            );
            rubi_star(&k / &e__, substituted)
        },
    ));
}

fn push_rules_rule_617(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 617,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p,x^m*(c+d*x)^n,x],x] /;
        FreeQ[{a,b,c,d,p},x] && ILtQ[n,0] && IntegerQ[m] && IntegerQ[2*p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && iltq!(n_, 0)
                && integerq!(m_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let second = x_.pow(&m_) * (&c__ + &d__ * x_).pow(&n_);
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_618(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 618,
        source: "Int[Sqrt[e_.*x_]/((c_+d_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          e/d \\[Star] Int[1/(Sqrt[e*x]*Sqrt[a+b*x^2]),x] -
          c*e/d \\[Star] Int[1/(Sqrt[e*x]*(c+d*x)*Sqrt[a+b*x^2]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ * x_).sqrt()
            / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let common = (&e__ * x_).sqrt() * (&a__ + &b__ * x_.pow(2)).sqrt();
            let first = rubi_rhs_int(&(Atom::num(1) / &common), x_);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (common * (&c__ + &d__ * x_))),
                x_,
            );
            rubi_star(&e__ / &d__, first)
                    - rubi_star(&c__ * &e__ / &d__, second)
        },
    ));
}

fn push_rules_rule_619(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 619,
        source: "Int[1/(Sqrt[e_.*x_]*(c_+d_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          1/Sqrt[a] \\[Star] Int[1/(Sqrt[e*x]*(c+d*x)*Sqrt[1-Rt[-b/a,2]*x]*Sqrt[1+Rt[-b/a,2]*x]),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && gtq!(a__, 0) },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&e__ * x_).sqrt()
                        * (&c__ + &d__ * x_)
                        * (Atom::num(1) - &q * x_).sqrt()
                        * (Atom::num(1) + q * x_).sqrt())),
                x_,
            );
            rubi_star(Atom::num(1) / a__.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_620(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 620,
        source: "Int[1/(Sqrt[e_.*x_]*(c_+d_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[1/(Sqrt[e*x]*(c+d*x)*Sqrt[1+b*x^2/a]),x] /;
        FreeQ[{a,b,c,d,e},x] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && !gtq!(a__, 0) },
        rhs: {
            let normalized_quadratic = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&e__ * x_).sqrt()
                        * (&c__ + &d__ * x_)
                        * normalized_quadratic.sqrt())),
                x_,
            );
            let coefficient = normalized_quadratic.sqrt()
                / (&a__ + &b__ * x_.pow(2)).sqrt();
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_621(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 621,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          c \\[Star] Int[x^m*(a+b*x^2)^p/(c^2-d^2*x^2),x] - d \\[Star] Int[x^(m+1)*(a+b*x^2)^p/(c^2-d^2*x^2),x] /;
        FreeQ[{a,b,c,d,m,p},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, p_], x_) },
        rhs: {
            let denominator = c__.pow(2) - d__.pow(2) * x_.pow(2);
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let first = rubi_rhs_int(
                &(x_.pow(&m_) * &quadratic_power / &denominator),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_.pow(&m_ + 1) * quadratic_power / denominator),
                x_,
            );
            rubi_star(c__, first) - rubi_star(d__, second)
        },
    ));
}

fn push_rules_rule_622(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 622,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(a+b*x^2)^p,(c/(c^2-d^2*x^2)-d*x/(c^2-d^2*x^2))^(-n),x],x] /;
        FreeQ[{a,b,c,d,m,p},x] && ILtQ[n,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_) && iltq!(n_, -1)
        },
        rhs: {
            let denominator = c__.pow(2) - d__.pow(2) * x_.pow(2);
            let first = x_.pow(&m_) * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let second = (&c__ / &denominator - &d__ * x_ / denominator).pow(-&n_);
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_623(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 623,
        source: "Int[(e_*x_)^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (e*x)^m/x^m \\[Star] Int[x^m*(c+d*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_) && iltq!(n_, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&c__ + &d__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let coefficient = (&e__ * x_).pow(&m_) / x_.pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_624(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 624,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          1/d \\[Star] Int[x^(m-1)*(c+d*x)^(n+1)*(a+b*x^2)^p,x] - c/d \\[Star] Int[x^(m-1)*(c+d*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && igtq!(m_, 0)
        },
        rhs: {
            let first = rubi_rhs_int(
                &(x_.pow(&m_ - 1)
                    * (&c__ + &d__ * x_).pow(&n_ + 1)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_.pow(&m_ - 1)
                    * (&c__ + &d__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / &d__, first)
                    - rubi_star(&c__ / &d__, second)
        },
    ));
}

fn push_rules_rule_625(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 625,
        source: "Int[Sqrt[a_+b_.*x_^2]/(x_*Sqrt[c_+d_.*x_]),x_Symbol] :=
          -2 \\[Star] Subst[Int[Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2]/(c-x^2),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).sqrt() / (x_ * (c__ + d__ * x_).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let radicand = (&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2);
            let primitive = rubi_rhs_int(
                &(radicand.sqrt() / (&c__ - sub_atom.pow(2))),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_626(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 626,
        source: "Int[(c_+d_.*x_)^n_*Sqrt[a_+b_.*x_^2]/x_,x_Symbol] :=
          a*c^(n+1/2) \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] +
          Int[1/(Sqrt[c+d*x]*Sqrt[a+b*x^2])*ExpandToSum[(-a*c^(n+1/2)+a*(c+d*x)^(n+1/2)+b*x^2*(c+d*x)^(n+1/2))/x,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n+3/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(&n_ + Atom::num(3) / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (x_ * linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let half_power = linear.pow(&n_ + Atom::num(1) / 2);
            let payload = rubi_expand_to_sum(
                &((-&a__ * c__.pow(&n_ + Atom::num(1) / 2)
                    + &a__ * &half_power
                    + &b__ * x_.pow(2) * half_power)
                    / x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(payload / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&a__ * c__.pow(&n_ + Atom::num(1) / 2), first) + second
        },
    ));
}

fn push_rules_rule_627(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 627,
        source: "Int[(c_+d_.*x_)^n_*Sqrt[a_+b_.*x_^2]/x_,x_Symbol] :=
          a*c^(n+1/2) \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] +
          Int[(c+d*x)^n/Sqrt[a+b*x^2]*ExpandToSum[(a+b*x^2-a*c^(n+1/2)*(c+d*x)^(-n-1/2))/x,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[n+1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(&n_ + Atom::num(1) / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (x_ * linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &((&a__ + &b__ * x_.pow(2)
                    - &a__
                        * c__.pow(&n_ + Atom::num(1) / 2)
                        * linear.pow(-&n_ - Atom::num(1) / 2))
                    / x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&n_) * payload / quadratic.sqrt()),
                x_,
            );
            rubi_star(&a__ * c__.pow(&n_ + Atom::num(1) / 2), first) + second
        },
    ));
}

fn push_rules_rule_628(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 628,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_*Sqrt[a_+b_.*x_^2],x_Symbol] :=
          c^(n-1/2)*(e*x)^(m+1)*Sqrt[c+d*x]*Sqrt[a+b*x^2]/(e*(m+1)) -
          1/(2*e*(m+1)) \\[Star] Int[(e*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[a+b*x^2])*
            ExpandToSum[(2*a*c^(n+1/2)*(m+1)+a*c^(n-1/2)*d*(2*m+3)*x+2*b*c^(n+1/2)*(m+2)*x^2+b*c^(n-1/2)*d*(2*m+5)*x^3-
              2*a*(m+1)*(c+d*x)^(n+1/2)-2*b*(m+1)*x^2*(c+d*x)^(n+1/2))/x,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n+3/2,0] && LtQ[m,-1] && IntegerQ[2*m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            * (c__ + d__ * x_).pow(n_)
            * (a__ + b__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(&n_ + Atom::num(3) / 2, 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = c__.pow(&n_ - Atom::num(1) / 2)
                * ex.pow(&m_ + 1)
                * linear.sqrt()
                * quadratic.sqrt()
                / (&e__ * (&m_ + 1));
            let payload = rubi_expand_to_sum(
                &((Atom::num(2)
                    * &a__
                    * c__.pow(&n_ + Atom::num(1) / 2)
                    * (&m_ + 1)
                    + &a__
                        * c__.pow(&n_ - Atom::num(1) / 2)
                        * &d__
                        * (Atom::num(2) * &m_ + 3)
                        * x_
                    + Atom::num(2)
                        * &b__
                        * c__.pow(&n_ + Atom::num(1) / 2)
                        * (&m_ + 2)
                        * x_.pow(2)
                    + &b__
                        * c__.pow(&n_ - Atom::num(1) / 2)
                        * &d__
                        * (Atom::num(2) * &m_ + 5)
                        * x_.pow(3)
                    - Atom::num(2)
                        * &a__
                        * (&m_ + 1)
                        * linear.pow(&n_ + Atom::num(1) / 2)
                    - Atom::num(2)
                        * &b__
                        * (&m_ + 1)
                        * x_.pow(2)
                        * linear.pow(&n_ + Atom::num(1) / 2))
                    / x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * payload / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let coefficient = Atom::num(1) / (Atom::num(2) * &e__ * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_629(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 629,
        source: "Int[(e_.*x_)^m_.*Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2],x_Symbol] :=
          2*(e*x)^(m+1)*Sqrt[c+d*x]*Sqrt[a+b*x^2]/(e*(2*m+5)) +
          1/(2*m+5) \\[Star] Int[(e*x)^m*(3*a*c+2*a*d*x+b*c*x^2)/(Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && Not[LtQ[m,-1]] && IntegerQ[2*m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            * (c__ + d__ * x_).sqrt()
            * (a__ + b__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && !ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &m_ + 5;
            let direct = Atom::num(2)
                * ex.pow(&m_ + 1)
                * linear.sqrt()
                * quadratic.sqrt()
                / (&e__ * &denominator);
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_)
                    * (Atom::num(3) * &a__ * &c__
                        + Atom::num(2) * &a__ * &d__ * x_
                        + &b__ * &c__ * x_.pow(2))
                    / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_630(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 630,
        source: "Int[Sqrt[c_+d_.*x_]/(x_*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -2 \\[Star] Subst[Int[x^2/((c-x^2)*Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2]),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let radicand = (&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(2) / ((&c__ - sub_atom.pow(2)) * radicand.sqrt())),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_631(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 631,
        source: "Int[1/(x_*Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -2 \\[Star] Subst[Int[1/((c-x^2)*Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2]),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let radicand = (&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / ((&c__ - sub_atom.pow(2)) * radicand.sqrt())),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_632(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 632,
        source: "Int[1/(x_*Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          1/Sqrt[a] \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[1-q*x]*Sqrt[1+q*x]),x]] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && negq!(&b__ / &a__) && gtq!(a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / (x_
                        * (&c__ + &d__ * x_).sqrt()
                        * (Atom::num(1) - &q * x_).sqrt()
                        * (Atom::num(1) + q * x_).sqrt())),
                x_,
            );
            rubi_star(Atom::num(1) / a__.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_633(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 633,
        source: "Int[1/(x_*Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[1+b*x^2/a]),x] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&b__ / &a__)
                && !gtq!(a__, 0)
        },
        rhs: {
            let normalized_quadratic = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / (x_
                        * (&c__ + &d__ * x_).sqrt()
                        * normalized_quadratic.sqrt())),
                x_,
            );
            let coefficient = normalized_quadratic.sqrt()
                / (&a__ + &b__ * x_.pow(2)).sqrt();
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_634(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 634,
        source: "Int[(c_+d_.*x_)^n_/(x_*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          c^(n+1/2) \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] -
          Int[1/(Sqrt[c+d*x]*Sqrt[a+b*x^2])*ExpandToSum[(c^(n+1/2)-(c+d*x)^(n+1/2))/x,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n-1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(&n_ - Atom::num(1) / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (x_ * linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &((c__.pow(&n_ + Atom::num(1) / 2)
                    - linear.pow(&n_ + Atom::num(1) / 2))
                    / x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(payload / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(c__.pow(&n_ + Atom::num(1) / 2), first) - second
        },
    ));
}

fn push_rules_rule_635(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 635,
        source: "Int[(c_+d_.*x_)^n_/(x_*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          c^(n+1/2) \\[Star] Int[1/(x*Sqrt[c+d*x]*Sqrt[a+b*x^2]),x] +
          Int[(c+d*x)^n/Sqrt[a+b*x^2]*ExpandToSum[(1-c^(n+1/2)*(c+d*x)^(-n-1/2))/x,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[n+1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(&n_ + Atom::num(1) / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (x_ * linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &((Atom::num(1)
                    - c__.pow(&n_ + Atom::num(1) / 2)
                        * linear.pow(-&n_ - Atom::num(1) / 2))
                    / x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&n_) * payload / quadratic.sqrt()),
                x_,
            );
            rubi_star(c__.pow(&n_ + Atom::num(1) / 2), first) + second
        },
    ));
}

fn push_rules_rule_636(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 636,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_)^n_/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          c^(n-1/2)*(e*x)^(m+1)*Sqrt[c+d*x]*Sqrt[a+b*x^2]/(a*e*(m+1)) -
          1/(2*a*e*(m+1)) \\[Star] Int[(e*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[a+b*x^2])*
             ExpandToSum[(2*a*c^(n+1/2)*(m+1)+a*c^(n-1/2)*d*(2*m+3)*x+2*b*c^(n+1/2)*(m+2)*x^2+b*c^(n-1/2)*d*(2*m+5)*x^3-2*a*(m+1)*(c+d*x)^(n+1/2))/x,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n+3/2,0] && LtQ[m,-1] && IntegerQ[2*m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
            / (a__ + b__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(&n_ + Atom::num(3) / 2, 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let ex = &e__ * x_;
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = c__.pow(&n_ - Atom::num(1) / 2)
                * ex.pow(&m_ + 1)
                * linear.sqrt()
                * quadratic.sqrt()
                / (&a__ * &e__ * (&m_ + 1));
            let payload = rubi_expand_to_sum(
                &((Atom::num(2)
                    * &a__
                    * c__.pow(&n_ + Atom::num(1) / 2)
                    * (&m_ + 1)
                    + &a__
                        * c__.pow(&n_ - Atom::num(1) / 2)
                        * &d__
                        * (Atom::num(2) * &m_ + 3)
                        * x_
                    + Atom::num(2)
                        * &b__
                        * c__.pow(&n_ + Atom::num(1) / 2)
                        * (&m_ + 2)
                        * x_.pow(2)
                    + &b__
                        * c__.pow(&n_ - Atom::num(1) / 2)
                        * &d__
                        * (Atom::num(2) * &m_ + 5)
                        * x_.pow(3)
                    - Atom::num(2)
                        * &a__
                        * (&m_ + 1)
                        * linear.pow(&n_ + Atom::num(1) / 2))
                    / x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(ex.pow(&m_ + 1) * payload / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let coefficient =
                Atom::num(1) / (Atom::num(2) * &a__ * &e__ * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_637(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 637,
        source: "Int[x_^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p/Sqrt[c+d*x],x^m*(c+d*x)^(n+1/2),x],x] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[p+1/2] && IntegerQ[n+1/2] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(&p_ + Atom::num(1) / 2)
                && integerq!(&n_ + Atom::num(1) / 2)
                && integerq!(m_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let first = (&a__ + &b__ * x_.pow(2)).pow(&p_) / linear.sqrt();
            let second = x_.pow(&m_) * linear.pow(&n_ + Atom::num(1) / 2);
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_638(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 638,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Unintegrable[(e*x)^m*(c+d*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_)
                    * (&c__ + &d__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn section_starts_with_consecutive_downvalue_orders() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let mut orders = rules
            .iter()
            .map(|rule| {
                rule.downvalue_order
                    .expect("section rule must have an order")
            })
            .collect::<Vec<_>>();
        orders.sort_unstable();

        let expected = (516..=554).chain(556..=638).collect::<Vec<_>>();
        assert_eq!(orders, expected);
    }

    #[test]
    fn downvalue_587_repeated_optional_x_still_requires_the_integration_variable() {
        let x = symbol!("x");
        let x_atom = Atom::var(x);
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let rule = Box::leak(Box::new(
            rules
                .into_iter()
                .find(|rule| rule.downvalue_order == Some(587))
                .expect("DownValue 587 must be present"),
        ));
        let denominator =
            (Atom::num(1) + Atom::num(2) * &x_atom) * (Atom::num(3) + Atom::num(4) * x_atom.pow(2));

        assert!(matcher_rule(&x_atom / &denominator, x, rule).is_some());
        assert!(matcher_rule(Atom::num(1) / denominator, x, rule).is_none());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).sqrt() / x_
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(n_) / (x_ * (a__ + b__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * x_).sqrt() / (x_ * (a__ + b__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_) / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow(p_)
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / ((e__ * x_).sqrt() * (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / (x_ * (c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_ * (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2)).pow((3, 2))
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    x_ / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow((3, 4)))
}
