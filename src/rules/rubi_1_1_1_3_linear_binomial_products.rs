use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_82(rules);
    push_rules_rule_83(rules);
    push_rules_rule_84(rules);
    push_rules_rule_85(rules);
    push_rules_rule_86(rules);
    push_rules_rule_87(rules);
    push_rules_rule_88(rules);
    push_rules_rule_89(rules);
    push_rules_rule_90(rules);
    push_rules_rule_91(rules);
    push_rules_rule_92(rules);
    push_rules_rule_93(rules);
    push_rules_rule_94(rules);
    push_rules_rule_95(rules);
    push_rules_rule_96(rules);
    push_rules_rule_97(rules);
    push_rules_rule_98(rules);
    push_rules_rule_99(rules);
    push_rules_rule_100(rules);
    push_rules_rule_101(rules);
    push_rules_rule_102(rules);
    push_rules_rule_103(rules);
    push_rules_rule_104(rules);
    push_rules_rule_105(rules);
    push_rules_rule_106(rules);
    push_rules_rule_107(rules);
    push_rules_rule_108(rules);
    push_rules_rule_109(rules);
    push_rules_rule_110(rules);
    push_rules_rule_111(rules);
    push_rules_rule_112(rules);
    push_rules_rule_113(rules);
    push_rules_rule_114(rules);
    push_rules_rule_115(rules);
    push_rules_rule_116(rules);
    push_rules_rule_117(rules);
    push_rules_rule_118(rules);
    push_rules_rule_119(rules);
    push_rules_rule_120(rules);
    push_rules_rule_121(rules);
    push_rules_rule_122(rules);
    push_rules_rule_123(rules);
    push_rules_rule_124(rules);
    push_rules_rule_125(rules);
    push_rules_rule_126(rules);
    push_rules_rule_127(rules);
    push_rules_rule_128(rules);
    push_rules_rule_129(rules);
    push_rules_rule_130(rules);
    push_rules_rule_131(rules);
    push_rules_rule_132(rules);
    push_rules_rule_133(rules);
    push_rules_rule_134(rules);
    push_rules_rule_135(rules);
    push_rules_rule_136(rules);
    push_rules_rule_137(rules);
    push_rules_rule_138(rules);
    push_rules_rule_139(rules);
    push_rules_rule_140(rules);
    push_rules_rule_141(rules);
    push_rules_rule_142(rules);
    push_rules_rule_143(rules);
    push_rules_rule_144(rules);
    push_rules_rule_145(rules);
    push_rules_rule_146(rules);
    push_rules_rule_147(rules);
    push_rules_rule_148(rules);
    push_rules_rule_149(rules);
    push_rules_rule_150(rules);
    push_rules_rule_151(rules);
    push_rules_rule_152(rules);
    push_rules_rule_153(rules);
    push_rules_rule_154(rules);
    push_rules_rule_155(rules);
    push_rules_rule_156(rules);
    push_rules_rule_157(rules);
    push_rules_rule_158(rules);
}

fn push_rules_rule_82(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 82,
        source: "Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          Int[(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[n,m] && IntegerQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(n_, m_)
                && integerq!(m_)
        },
        rhs: {
            rubi_rhs_int(
                &((a__ * c__ + b__ * d__ * x_.pow(2)).pow(m_) * (e__ + f__ * x_).pow(p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_83(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 83,
        source: "Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0] && EqQ[a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && neq!(&n_ + &p_ + Atom::num(2), Atom::num(0))
                && eqq!(
                    &a__ * &d__ * &f__ * (&n_ + &p_ + Atom::num(2))
                        - &b__
                            * (&d__ * &e__ * (&n_ + Atom::num(1))
                                + &c__ * &f__ * (&p_ + Atom::num(1))),
                    Atom::num(0)
                )
        },
        rhs: {
            let n_p_2 = &n_ + &p_ + Atom::num(2);
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            rubi_simp(&(&b__ * cdx.pow(&n_ + Atom::num(1)) * efx.pow(&p_ + Atom::num(1))
                    / (&d__ * &f__ * n_p_2)), x_)
        },
    ));
}

fn push_rules_rule_84(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 84,
        source: "Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_] :=
          Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && IGtQ[p,0] && EqQ[b*e+a*f,0] && Not[ILtQ[n+p+2,0] && GtQ[n+2*p,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, d__, e__, f__, n_, p_, x_],
        optional: [b__, d__, f__, n_, p_],
        x_free: [a__, b__, d__, e__, f__, n_],
        integer_gt: [(p_, 0)],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && igtq!(p_, 0)
                && eqq!(&b__ * &e__ + &a__ * &f__, Atom::num(0))
                && !(iltq!(&n_ + &p_ + Atom::num(2), 0)
                    && gtq!(&n_ + Atom::num(2) * &p_, 0))
        },
        rhs: {
            let integrand = (a__ + b__ * x_) * (d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_85(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 85,
        source: "Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_] :=
          Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && IGtQ[p,0] && (NeQ[n,-1] || EqQ[p,1]) && NeQ[b*e+a*f,0] &&
          (Not[IntegerQ[n]] || LtQ[9*p+5*n,0] || GeQ[n+p+1,0] || GeQ[n+p+2,0] && RationalQ[a,b,d,e,f]) && (NeQ[n+p+3,0] || EqQ[p,1])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, d__, e__, f__, n_, p_, x_],
        optional: [b__, d__, f__, n_, p_],
        x_free: [a__, b__, d__, e__, f__, n_],
        integer_gt: [(p_, 0)],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && igtq!(p_, 0)
                && (neq!(n_, -Atom::num(1)) || eqq!(p_, Atom::num(1)))
                && neq!(&b__ * &e__ + &a__ * &f__, Atom::num(0))
                && (!integerq!(n_)
                    || ltq!(Atom::num(9) * &p_ + Atom::num(5) * &n_, 0)
                    || geq!(&n_ + &p_ + Atom::num(1), 0)
                    || geq!(&n_ + &p_ + Atom::num(2), 0)
                        && rationalq!([a__, b__, d__, e__, f__]))
                && (neq!(&n_ + &p_ + Atom::num(3), Atom::num(0))
                    || eqq!(p_, Atom::num(1)))
        },
        rhs: {
            let integrand = (a__ + b__ * x_) * (d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_86(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 86,
        source: "Int[(a_.+b_.*x_)*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          Int[ExpandIntegrand[(a+b*x)*(c+d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && (ILtQ[n,0] && ILtQ[p,0] || EqQ[p,1] ||
            IGtQ[p,0] && (Not[IntegerQ[n]] || LeQ[9*p+5*(n+2),0] || GeQ[n+p+1,0] || GeQ[n+p+2,0] && RationalQ[a,b,c,d,e,f]))",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && (iltq!(n_, 0) && iltq!(p_, 0)
                    || eqq!(p_, Atom::num(1))
                    || igtq!(p_, 0)
                        && (!integerq!(n_)
                            || leq!(
                                Atom::num(9) * &p_
                                    + Atom::num(5) * (&n_ + Atom::num(2)),
                                0
                            )
                            || geq!(&n_ + &p_ + Atom::num(1), 0)
                            || geq!(&n_ + &p_ + Atom::num(2), 0)
                                && rationalq!([a__, b__, c__, d__, e__, f__])))
        },
        rhs: {
            let integrand = (a__ + b__ * x_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_87(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 87,
        source: "Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) -
          (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e)) \\[Star] Int[(c+d*x)^n*(e+f*x)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && LtQ[p,-1] &&
          (Not[LtQ[n,-1]] || IntegerQ[p] || Not[IntegerQ[n] || Not[EqQ[e,0] || Not[EqQ[c,0] || LtQ[p,n]]]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && ltq!(p_, -1)
                && (!ltq!(n_, -1)
                    || integerq!(p_)
                    || !(integerq!(n_)
                        || !(eqq!(e__, Atom::num(0))
                            || !(eqq!(c__, Atom::num(0)) || ltq!(p_, n_)))))
        },
        rhs: {
            let n_p_2 = &n_ + &p_ + Atom::num(2);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let cf_de = &c__ * &f__ - &d__ * &e__;
            let coeff =
                (&a__ * &d__ * &f__ * &n_p_2 - &b__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    .expand();
            let be_af = &b__ * &e__ - &a__ * &f__;
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let rest = rubi_rhs_int(
                &(cdx.pow(&n_) * efx.pow(&p1)),
                x_,
            );
            let direct = -be_af * cdx.pow(&n_ + Atom::num(1)) * efx.pow(&p1)
                / (&f__ * &p1 * &cf_de);
            rubi_simp(&(direct), x_) - rubi_star(coeff / (&f__ * p1 * cf_de), rest)
        },
    ));
}

fn push_rules_rule_88(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 88,
        source: "Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) -
          (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e)) \\[Star] Int[(c+d*x)^n*(e+f*x)^Simplify[p+1],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && Not[RationalQ[p]] && SumSimplerQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && !rationalq!(p_)
                && sum_simplerq!(p_, 1)
        },
        rhs: {
            let n_p_2 = &n_ + &p_ + Atom::num(2);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let cf_de = &c__ * &f__ - &d__ * &e__;
            let coeff =
                (&a__ * &d__ * &f__ * &n_p_2 - &b__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    .expand();
            let be_af = &b__ * &e__ - &a__ * &f__;
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let simplified_p1 = rubi_simplify(&p1);
            let rest = rubi_rhs_int(&(cdx.pow(&n_) * efx.pow(&simplified_p1)), x_);
            let direct = -be_af * cdx.pow(&n_ + Atom::num(1)) * efx.pow(&p1)
                / (&f__ * &p1 * &cf_de);
            rubi_simp(&(direct), x_) - rubi_star(coeff / (&f__ * p1 * cf_de), rest)
        },
    ));
}

fn push_rules_rule_89(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 89,
        source: "Int[(a_.+b_.*x_)*Sqrt[c_+d_.*x_]/Sqrt[e_+f_.*x_],x_] :=
          Sqrt[c*e]*(b*f*x-2*(b*e-a*f))*Sqrt[e^2-f^2*x^2]/(2*e*f^2) - Sqrt[c*e]*(b*e-2*a*f)*ArcSin[f*x/e]/(2*f^2) /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[d*e+c*f,0] && GtQ[c,0] && GtQ[e,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * x_) * (c__ + d__ * x_).sqrt() / (e__ + f__ * x_).sqrt(),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
        },
        rhs: {
            let sqrt_ce = (&c__ * &e__).sqrt();
            let sqrt_difference = (e__.pow(2) - f__.pow(2) * x_.pow(2)).sqrt();
            rubi_simp(&(&sqrt_ce
                    * (&b__ * &f__ * x_ - Atom::num(2) * (&b__ * &e__ - &a__ * &f__))
                    * sqrt_difference
                    / (Atom::num(2) * &e__ * f__.pow(2))), x_)
                    - rubi_simp(&(&sqrt_ce * (&b__ * &e__ - Atom::num(2) * &a__ * &f__)
                        * (&f__ * x_ / &e__).asin()
                        / (Atom::num(2) * f__.pow(2))), x_)
        },
    ));
}

fn push_rules_rule_90(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 90,
        source: "Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) +
          (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(d*f*(n+p+2)) \\[Star] Int[(c+d*x)^n*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && neq!(&n_ + &p_ + Atom::num(2), Atom::num(0))
        },
        rhs: {
            let n_p_2 = &n_ + &p_ + Atom::num(2);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let coeff =
                (&a__ * &d__ * &f__ * &n_p_2 - &b__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    .expand();
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let rest = rubi_rhs_int(&(cdx.pow(&n_) * efx.pow(&p_)), x_);
            let direct = &b__ * cdx.pow(&n_ + Atom::num(1)) * efx.pow(&p_ + Atom::num(1))
                / (&d__ * &f__ * &n_p_2);
            rubi_simp(&(direct), x_) + rubi_star(coeff / (&d__ * &f__ * n_p_2), rest)
        },
    ));
}

fn push_rules_rule_91(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 91,
        source: "Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(c+d*x)^(n+1)*(e+f*x)^(p+1)*(2*a*d*f*(n+p+3)-b*(d*e*(n+2)+c*f*(p+2))+b*d*f*(n+p+2)*x)/(d^2*f^2*(n+p+2)*(n+p+3)) /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0] && NeQ[n+p+3,0] &&
          EqQ[d*f*(n+p+2)*(a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1))))-b*(d*e*(n+1)+c*f*(p+1))*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2))),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && neq!(&n_ + &p_ + Atom::num(2), Atom::num(0))
                && neq!(&n_ + &p_ + Atom::num(3), Atom::num(0))
                && eqq!(
                    &d__ * &f__
                        * (&n_ + &p_ + Atom::num(2))
                        * (a__.pow(2) * &d__ * &f__ * (&n_ + &p_ + Atom::num(3))
                            - &b__
                                * (&b__ * &c__ * &e__
                                    + &a__
                                        * (&d__ * &e__ * (&n_ + Atom::num(1))
                                            + &c__ * &f__ * (&p_ + Atom::num(1)))))
                        - &b__
                            * (&d__ * &e__ * (&n_ + Atom::num(1))
                                + &c__ * &f__ * (&p_ + Atom::num(1)))
                            * (&a__ * &d__ * &f__ * (&n_ + &p_ + Atom::num(4))
                                - &b__
                                    * (&d__ * &e__ * (&n_ + Atom::num(2))
                                        + &c__ * &f__ * (&p_ + Atom::num(2)))),
                    Atom::num(0)
                )
        },
        rhs: {
            let n_p_2 = &n_ + &p_ + Atom::num(2);
            let n_p_3 = &n_ + &p_ + Atom::num(3);
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let linear = Atom::num(2) * &a__ * &d__ * &f__ * &n_p_3
                - &b__ * (&d__ * &e__ * (&n_ + Atom::num(2)) + &c__ * &f__ * (&p_ + Atom::num(2)))
                + &b__ * &d__ * &f__ * &n_p_2 * x_;
            rubi_simp(&(&b__ * cdx.pow(&n_ + Atom::num(1)) * efx.pow(&p_ + Atom::num(1))
                    * linear
                    / (d__.pow(2) * f__.pow(2) * n_p_2 * n_p_3)), x_)
        },
    ));
}

fn push_rules_rule_92(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, f__);
    rules.push(rubi_rule!(
        order: 92,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(f_.*x_)^p_,x_] :=
           a \\[Star] Int[(a+b*x)^n*(c+d*x)^n*(f*x)^p,x] + b/f \\[Star] Int[(a+b*x)^n*(c+d*x)^n*(f*x)^(p+1),x] /;
        FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[m-n-1,0] && Not[RationalQ[p]] && Not[IGtQ[m,0]] && NeQ[m+n+p+2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(&m_ - &n_ - Atom::num(1), Atom::num(0))
                && !rationalq!(p_)
                && !igtq!(m_, 0)
                && neq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let scaled_x = &f__ * x_;
            let common = first.pow(&n_) * second.pow(&n_);
            let first = rubi_rhs_int(&(&common * scaled_x.pow(&p_)), x_);
            let second = rubi_rhs_int(&(common * scaled_x.pow(&p_ + Atom::num(1))), x_);
            rubi_star(a__, first) + rubi_star(&b__ / &f__, second)
        },
    ));
}

fn push_rules_rule_93(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 93,
        source: "Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          Int[ExpandIntegrand[(e+f*x)^p/((a+b*x)*(c+d*x)),x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_) && integerq!(p_)
        },
        rhs: {
            let integrand =
                (&e__ + &f__ * x_).pow(p_) / ((&a__ + &b__ * x_) * (&c__ + &d__ * x_));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_94(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 94,
        source: "Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[(e+f*x)^(p-1)/(a+b*x),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[(e+f*x)^(p-1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f},x] && LtQ[0,p,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && ltq!(0, p_, 1)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let efx = &e__ + &f__ * x_;
            let first = rubi_rhs_int(
                &(efx.pow(&p_ - Atom::num(1)) / (&a__ + &b__ * x_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(efx.pow(&p_ - Atom::num(1)) / (&c__ + &d__ * x_)),
                x_,
            );
            rubi_star((&b__ * &e__ - &a__ * &f__) / &det, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / det, second)
        },
    ));
}

fn push_rules_rule_95(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 95,
        source: "Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          f*(e+f*x)^(p-1)/(b*d*(p-1)) +
         1/(b*d) \\[Star] Int[(b*d*e^2-a*c*f^2+f*(2*b*d*e-b*c*f-a*d*f)*x)*(e+f*x)^(p-2)/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(p_, 1)
        },
        rhs: {
            let efx = &e__ + &f__ * x_;
            let p1 = &p_ - Atom::num(1);
            let p2 = &p_ - Atom::num(2);
            let bd = &b__ * &d__;
            let polynomial = &b__ * &d__ * e__.pow(2) - &a__ * &c__ * f__.pow(2)
                + &f__
                    * (Atom::num(2) * &b__ * &d__ * &e__
                        - &b__ * &c__ * &f__
                        - &a__ * &d__ * &f__)
                    * x_;
            let rest = rubi_rhs_int(
                &(polynomial * efx.pow(p2) / ((&a__ + &b__ * x_) * (&c__ + &d__ * x_))),
                x_,
            );
            rubi_simp(&(&f__ * efx.pow(&p1) / (&bd * &p1)), x_)
                    + rubi_star(Atom::num(1) / bd, rest)
        },
    ));
}

fn push_rules_rule_96(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 96,
        source: "Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          f*(e+f*x)^(p+1)/((p+1)*(b*e-a*f)*(d*e-c*f)) +
          1/((b*e-a*f)*(d*e-c*f)) \\[Star] Int[(b*d*e-b*c*f-a*d*f-b*d*f*x)*(e+f*x)^(p+1)/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && ltq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let efx = &e__ + &f__ * x_;
            let first_cross = &b__ * &e__ - &a__ * &f__;
            let second_cross = &d__ * &e__ - &c__ * &f__;
            let denominator = &first_cross * &second_cross;
            let polynomial =
                &b__ * &d__ * &e__ - &b__ * &c__ * &f__ - &a__ * &d__ * &f__ - &b__ * &d__ * &f__ * x_;
            let rest = rubi_rhs_int(
                &(polynomial * efx.pow(&p1) / ((&a__ + &b__ * x_) * (&c__ + &d__ * x_))),
                x_,
            );
            rubi_simp(&(&f__ * efx.pow(&p1) / (&p1 * &denominator)), x_)
                    + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_97(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 97,
        source: "Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          b/(b*c-a*d) \\[Star] Int[(e+f*x)^p/(a+b*x),x] -
          d/(b*c-a*d) \\[Star] Int[(e+f*x)^p/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && Not[IntegerQ[p]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let efx_p = (&e__ + &f__ * x_).pow(p_);
            let first = rubi_rhs_int(&(&efx_p / (&a__ + &b__ * x_)), x_);
            let second = rubi_rhs_int(&(efx_p / (&c__ + &d__ * x_)), x_);
            rubi_star(&b__ / &det, first)
                    - rubi_star(&d__ / det, second)
        },
    ));
}

fn push_rules_rule_98(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 98,
        source: "Int[(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_/(a_.+b_.*x_),x_] :=
          Int[ExpandIntegrand[(e+f*x)^FractionalPart[p],(c+d*x)^n*(e+f*x)^IntegerPart[p]/(a+b*x),x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,0] && LtQ[p,-1] && FractionQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_) * (a__ + b__ * x_).pow(-1),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && fractionq!(p_)
        },
        rhs: {
            let efx = &e__ + &f__ * x_;
            let expanded = rubi_expand_integrand_product(
                &efx.pow(rubi_frac_part(&p_)),
                &((&c__ + &d__ * x_).pow(n_) * efx.pow(rubi_int_part(&p_)) / (&a__ + &b__ * x_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_99(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 99,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && IntegersQ[m,n] && (IntegerQ[p] || GtQ[m,0] && GeQ[n,-1])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && integersq!([m_, n_])
                && (integerq!(p_) || gtq!(m_, 0) && geq!(n_, -1))
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 100,
        source: "Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (b*c-a*d)^2*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d^2*(d*e-c*f)*(n+1)) -
          1/(d^2*(d*e-c*f)*(n+1)) \\[Star] Int[(c+d*x)^(n+1)*(e+f*x)^p*
            Simp[a^2*d^2*f*(n+p+2)+b^2*c*(d*e*(n+1)+c*f*(p+1))-2*a*b*d*(d*e*(n+1)+c*f*(p+1))-b^2*d*(d*e-c*f)*(n+1)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && (LtQ[n,-1] || EqQ[n+p+3,0] && NeQ[n,-1] && (SumSimplerQ[n,1] || Not[SumSimplerQ[p,1]]))",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && (ltq!(n_, -1)
                    || eqq!(&n_ + &p_ + Atom::num(3), Atom::num(0))
                        && neq!(n_, -Atom::num(1))
                        && (sum_simplerq!(n_, 1) || !sum_simplerq!(p_, 1)))
        },
        rhs: {
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let cross = &d__ * &e__ - &c__ * &f__;
            let denominator = d__.pow(2) * &cross * &n1;
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let simp = simp!(
                a__.pow(2) * d__.pow(2) * &f__ * (&n_ + &p_ + Atom::num(2))
                    + b__.pow(2) * &c__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1)
                    - Atom::num(2) * &a__ * &b__ * &d__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1)
                    - b__.pow(2) * &d__ * &cross * &n1 * x_,
                x_
            );
            let rest = rubi_rhs_int(&(cdx.pow(&n1) * efx.pow(p_) * simp), x_);
            let direct = (&b__ * &c__ - &a__ * &d__).pow(2)
                * cdx.pow(&n1)
                * efx.pow(&p1)
                / &denominator;
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 101,
        source: "Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+3)) +
          1/(d*f*(n+p+3)) \\[Star] Int[(c+d*x)^n*(e+f*x)^p*
            Simp[a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+3,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && neq!(&n_ + &p_ + Atom::num(3), Atom::num(0))
        },
        rhs: {
            let n1 = &n_ + Atom::num(1);
            let n2 = &n_ + Atom::num(2);
            let p1 = &p_ + Atom::num(1);
            let p2 = &p_ + Atom::num(2);
            let n_p_3 = &n_ + &p_ + Atom::num(3);
            let n_p_4 = &n_ + &p_ + Atom::num(4);
            let cdx = &c__ + &d__ * x_;
            let efx = &e__ + &f__ * x_;
            let simp = simp!(
                a__.pow(2) * &d__ * &f__ * &n_p_3
                    - &b__ * (&b__ * &c__ * &e__ + &a__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    + &b__
                        * (&a__ * &d__ * &f__ * &n_p_4
                            - &b__ * (&d__ * &e__ * &n2 + &c__ * &f__ * &p2))
                        * x_,
                x_
            );
            let denominator = &d__ * &f__ * &n_p_3;
            let rest = rubi_rhs_int(&(cdx.pow(n_) * efx.pow(p_) * simp), x_);
            let direct = &b__ * (&a__ + &b__ * x_) * cdx.pow(&n1) * efx.pow(&p1)
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 102,
        source: "Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)*(e_.+f_.*x_)),x_] :=
          With[{q=Rt[(d*e-c*f)/(b*e-a*f),3]},
          -Sqrt[3]*q*ArcTan[1/Sqrt[3]+2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))]/(d*e-c*f) +
          q*Log[e+f*x]/(2*(d*e-c*f)) -
          3*q*Log[q*(a+b*x)^(1/3)-(c+d*x)^(1/3)]/(2*(d*e-c*f))] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_).pow((1, 3))
                * (c__ + d__ * x_).pow((2, 3))
                * (e__ + f__ * x_)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
        },
        rhs: {
            let q = rubi_rt(&((&d__ * &e__ - &c__ * &f__) / (&b__ * &e__ - &a__ * &f__)), 3);
            let sqrt3 = Atom::num(3).sqrt();
            let first_root = (&a__ + &b__ * x_).pow(Atom::num(1) / Atom::num(3));
            let second_root = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            let den = &d__ * &e__ - &c__ * &f__;
            rubi_simp(&(-&sqrt3 * &q
                    * (Atom::num(1) / &sqrt3
                        + Atom::num(2) * &q * &first_root / (&sqrt3 * &second_root))
                        .atan()
                    / &den), x_)
                    + rubi_simp(&(&q * (&e__ + &f__ * x_).log() / (Atom::num(2) * &den)), x_)
                    - rubi_simp(&(Atom::num(3) * &q * (&q * first_root - second_root).log()
                        / (Atom::num(2) * den)), x_)
        },
    ));
}

fn push_rules_rule_103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 103,
        source: "Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)),x_] :=
          b*f \\[Star] Subst[Int[1/(d*(b*e-a*f)^2+b*f^2*x^2),x],x,Sqrt[a+b*x]*Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-f*(b*c+a*d),0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(
                    Atom::num(2) * &b__ * &d__ * &e__ - &f__ * (&b__ * &c__ + &a__ * &d__),
                    Atom::num(0)
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&d__ * (&b__ * &e__ - &a__ * &f__).pow(2) + &b__ * f__.pow(2) * sub.pow(2))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&a__ + &b__ * x_).sqrt() * (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(&b__ * &f__, substituted)
        },
    ));
}

fn push_rules_rule_104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 104,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_] :=
          With[{q=Denominator[m]},
          q \\[Star] Subst[Int[x^(q*(m+1)-1)/(b*e-a*f-(d*e-c*f)*x^q),x],x,(a+b*x)^(1/q)/(c+d*x)^(1/q)]] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[m+n+1,0] && RationalQ[n] && LtQ[-1,m,0] && SimplerQ[a+b*x,c+d*x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(-1),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&m_ + &n_ + Atom::num(1), Atom::num(0))
                && rationalq!(n_)
                && ltq!(-1, m_, 0)
                && simplerq!(
                    &a__ + &b__ * x_,
                    &c__ + &d__ * x_
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let q = Atom::num(denominator!(m_));
            let transformed = rubi_rhs_int(
                &(sub.pow(&q * (&m_ + Atom::num(1)) - Atom::num(1))
                    / (&b__ * &e__ - &a__ * &f__ - (&d__ * &e__ - &c__ * &f__) * sub.pow(&q))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &transformed,
                sub_symbol,
                (a__ + b__ * x_).pow(Atom::num(1) / &q)
                    / (c__ + d__ * x_).pow(Atom::num(1) / &q),
            );
            rubi_star(q, substituted)
        },
    ));
}

fn push_rules_rule_105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 105,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) -
          n*(d*e-c*f)/((m+1)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[m+n+p+2,0] && GtQ[n,0] && (SumSimplerQ[m,1] || Not[SumSimplerQ[p,1]]) && NeQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
                && gtq!(n_, 0)
                && (sum_simplerq!(m_, 1) || !sum_simplerq!(p_, 1))
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &m1 * (&b__ * &e__ - &a__ * &f__);
            let rest = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(&n_ - Atom::num(1)) * third.pow(&p_)),
                x_,
            );
            let direct = first.pow(&m1) * second.pow(&n_) * third.pow(&p1)
                / &denominator;
            rubi_simp(&(direct), x_)
                    - rubi_star(&n_ * (&d__ * &e__ - &c__ * &f__) / denominator, rest)
        },
    ));
}

fn push_rules_rule_106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 106,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[Simplify[m+n+p+3],0] && EqQ[a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1),0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + &n_ + &p_ + Atom::num(3))), 0)
                && eqq!(
                    &a__ * &d__ * &f__ * (&m_ + Atom::num(1))
                        + &b__ * &c__ * &f__ * (&n_ + Atom::num(1))
                        + &b__ * &d__ * &e__ * (&p_ + Atom::num(1)),
                    0
                )
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            rubi_simp(&(&b__ * (&a__ + &b__ * x_).pow(&m_ + Atom::num(1))
                    * (&c__ + &d__ * x_).pow(&n_ + Atom::num(1))
                    * (&e__ + &f__ * x_).pow(&p_ + Atom::num(1))
                    / ((&m_ + Atom::num(1))
                        * (&b__ * &c__ - &a__ * &d__)
                        * (&b__ * &e__ - &a__ * &f__))), x_)
        },
    ));
}

fn push_rules_rule_107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 107,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          (a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1))/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[Simplify[m+n+p+3],0] && (LtQ[m,-1] || SumSimplerQ[m,1])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(
                    rubi_simplify(&(&m_ + &n_ + &p_ + Atom::num(3))),
                    Atom::num(0)
                )
                && (ltq!(m_, -1) || sum_simplerq!(m_, 1))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &m1 * (&b__ * &c__ - &a__ * &d__) * (&b__ * &e__ - &a__ * &f__);
            let coefficient = &a__ * &d__ * &f__ * &m1 + &b__ * &c__ * &f__ * &n1 + &b__ * &d__ * &e__ * &p1;
            let rest = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(&n_) * third.pow(&p_)),
                x_,
            );
            let direct = &b__ * first.pow(&m1) * second.pow(&n1) * third.pow(&p1)
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(coefficient / denominator, rest)
        },
    ));
}

fn push_rules_rule_108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 108,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p/(b*(m+1)) -
          1/(b*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p-1)*Simp[d*e*n+c*f*p+d*f*(n+p)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && LtQ[m,-1] && GtQ[n,0] && GtQ[p,0] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && (integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_
                ]) || integersq!([m_, &n_ + &p_])
                    || integersq!([p_, &m_ + &n_]))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let simp = simp!(
                &d__ * &e__ * &n_ + &c__ * &f__ * &p_ + &d__ * &f__ * (&n_ + &p_) * x_,
                x_
            );
            let denominator = &b__ * &m1;
            let rest = rubi_rhs_int(
                &(first.pow(&m1)
                    * second.pow(&n_ - Atom::num(1))
                    * third.pow(&p_ - Atom::num(1))
                    * simp),
                x_,
            );
            let direct = first.pow(&m1) * second.pow(&n_) * third.pow(&p_)
                / &denominator;
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
                order: 109,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
                  (b*c-a*d)*(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) +
                  1/(b*(b*e-a*f)*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-2)*(e+f*x)^p*
                    Simp[a*d*(d*e*(n-1)+c*f*(p+1))+b*c*(d*e*(m-n+2)-c*f*(m+p+2))+d*(a*d*f*(n+p)+b*(d*e*(m+1)-c*f*(m+n+p+1)))*x,x],x] /;
                FreeQ[{a,b,c,d,e,f,p},x] && LtQ[m,-1] && GtQ[n,1] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_3(symbols),
                with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
                optional: [a__, b__, c__, d__, e__, f__],
                x_free: [a__, b__, c__, d__, e__, f__, p_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                        && ltq!(m_, -1)
                        && gtq!(n_, 1)
                        && (integersq!([
                            Atom::num(2) * &m_,
                            Atom::num(2) * &n_,
                            Atom::num(2) * &p_
                        ]) || integersq!([m_, &n_ + &p_])
                            || integersq!([p_, &m_ + &n_]))
                },
                rhs: {
                    let m1 = &m_ + Atom::num(1);
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let denominator = &b__ * (&b__ * &e__ - &a__ * &f__) * &m1;
                    let simp = simp!(
                        &a__ * &d__ * (&d__ * &e__ * (&n_ - Atom::num(1)) + &c__ * &f__ * (&p_ + Atom::num(1)))
                            + &b__ * &c__ * (&d__ * &e__ * (&m_ - &n_ + Atom::num(2)) - &c__ * &f__ * (&m_ + &p_ + Atom::num(2)))
                            + &d__
                                * (&a__ * &d__ * &f__ * (&n_ + &p_)
                                    + &b__ * (&d__ * &e__ * &m1 - &c__ * &f__ * (&m_ + &n_ + &p_ + Atom::num(1))))
                                * x_,
                        x_
                    );
                    let rest = rubi_rhs_int(
                        &(first.pow(&m1)
                            * second.pow(&n_ - Atom::num(2))
                            * third.pow(&p_)
                            * simp),
                        x_,
                    );
                    let direct = (&b__ * &c__ - &a__ * &d__)
                        * first.pow(&m1)
                        * second.pow(&n_ - Atom::num(1))
                        * third.pow(&p_ + Atom::num(1))
                        / &denominator;
                    rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
                },
            ));
}

fn push_rules_rule_110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 110,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) -
          1/((m+1)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
            Simp[d*e*n+c*f*(m+p+2)+d*f*(m+n+p+2)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && LtQ[m,-1] && GtQ[n,0] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && (integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_
                ]) || integersq!([m_, &n_ + &p_])
                    || integersq!([p_, &m_ + &n_]))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &m1 * (&b__ * &e__ - &a__ * &f__);
            let simp = simp!(
                &d__ * &e__ * &n_
                    + &c__ * &f__ * (&m_ + &p_ + Atom::num(2))
                    + &d__ * &f__ * (&m_ + &n_ + &p_ + Atom::num(2)) * x_,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(&m1)
                    * second.pow(&n_ - Atom::num(1))
                    * third.pow(&p_)
                    * simp),
                x_,
            );
            let direct = first.pow(&m1)
                * second.pow(&n_)
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 111,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) +
          1/(d*f*(m+n+p+1)) \\[Star] Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
            Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && GtQ[m,1] && NeQ[m+n+p+1,0] && IntegerQ[m]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_ + &p_ + Atom::num(1), Atom::num(0))
                && integerq!(m_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m_n_p_1 = &m_ + &n_ + &p_ + Atom::num(1);
            let denominator = &d__ * &f__ * &m_n_p_1;
            let simp = simp!(
                &a__ * &a__ * &d__ * &f__ * &m_n_p_1
                    - &b__
                        * (&b__ * &c__ * &e__ * (&m_ - Atom::num(1))
                            + &a__
                                * (&d__ * &e__ * (&n_ + Atom::num(1))
                                    + &c__ * &f__ * (&p_ + Atom::num(1))))
                    + &b__
                        * (&a__
                            * &d__
                            * &f__
                            * (Atom::num(2) * &m_ + &n_ + &p_)
                            - &b__
                                * (&d__ * &e__ * (&m_ + &n_)
                                    + &c__ * &f__ * (&m_ + &p_)))
                        * x_,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(&m_ - Atom::num(2))
                    * second.pow(&n_)
                    * third.pow(&p_)
                    * simp),
                x_,
            );
            let direct = &b__ * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 112,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^m*(c+d*x)^n*(e+f*x)^(p+1)/(f*(m+n+p+1)) -
          1/(f*(m+n+p+1)) \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^(n-1)*(e+f*x)^p*
            Simp[c*m*(b*e-a*f)+a*n*(d*e-c*f)+(d*m*(b*e-a*f)+b*n*(d*e-c*f))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && GtQ[m,0] && GtQ[n,0] && NeQ[m+n+p+1,0] && (IntegersQ[2*m,2*n,2*p] || (IntegersQ[m,n+p] || IntegersQ[p,m+n]))",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && gtq!(m_, 0)
                && gtq!(n_, 0)
                && neq!(&m_ + &n_ + &p_ + Atom::num(1), Atom::num(0))
                && (integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_
                ]) || integersq!([m_, &n_ + &p_])
                    || integersq!([p_, &m_ + &n_]))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m_n_p_1 = &m_ + &n_ + &p_ + Atom::num(1);
            let denominator = &f__ * &m_n_p_1;
            let b_e_a_f = &b__ * &e__ - &a__ * &f__;
            let d_e_c_f = &d__ * &e__ - &c__ * &f__;
            let simp = simp!(
                &c__ * &m_ * &b_e_a_f
                    + &a__ * &n_ * &d_e_c_f
                    + (&d__ * &m_ * &b_e_a_f + &b__ * &n_ * &d_e_c_f) * x_,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(&m_ - Atom::num(1))
                    * second.pow(&n_ - Atom::num(1))
                    * third.pow(&p_)
                    * simp),
                x_,
            );
            let direct = first.pow(&m_)
                * second.pow(&n_)
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 113,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) +
          1/(d*f*(m+n+p+1)) \\[Star] Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
            Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && GtQ[m,1] && NeQ[m+n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_ + &p_ + Atom::num(1), Atom::num(0))
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_
                ])
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m_n_p_1 = &m_ + &n_ + &p_ + Atom::num(1);
            let denominator = &d__ * &f__ * &m_n_p_1;
            let simp = simp!(
                &a__ * &a__ * &d__ * &f__ * &m_n_p_1
                    - &b__
                        * (&b__ * &c__ * &e__ * (&m_ - Atom::num(1))
                            + &a__
                                * (&d__ * &e__ * (&n_ + Atom::num(1))
                                    + &c__ * &f__ * (&p_ + Atom::num(1))))
                    + &b__
                        * (&a__
                            * &d__
                            * &f__
                            * (Atom::num(2) * &m_ + &n_ + &p_)
                            - &b__
                                * (&d__ * &e__ * (&m_ + &n_)
                                    + &c__ * &f__ * (&m_ + &p_)))
                        * x_,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(&m_ - Atom::num(2))
                    * second.pow(&n_)
                    * third.pow(&p_)
                    * simp),
                x_,
            );
            let direct = &b__ * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 114,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && ILtQ[m,-1] && (IntegerQ[n] || IntegersQ[2*n,2*p] || ILtQ[m+n+p+3,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && iltq!(m_, -1)
                && (integerq!(n_)
                    || integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                    || iltq!(&m_ + &n_ + &p_ + Atom::num(3), 0))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &m1 * (&b__ * &c__ - &a__ * &d__) * (&b__ * &e__ - &a__ * &f__);
            let simp = simp!(
                &a__ * &d__ * &f__ * &m1
                    - &b__
                        * (&d__ * &e__ * (&m_ + &n_ + Atom::num(2))
                            + &c__ * &f__ * (&m_ + &p_ + Atom::num(2)))
                    - &b__ * &d__ * &f__ * (&m_ + &n_ + &p_ + Atom::num(3)) * x_,
                x_
            );
            let direct = &b__ * first.pow(&m1)
                * second.pow(&n_ + Atom::num(1))
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            let rest = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(&n_) * third.pow(&p_) * simp),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 115,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
                freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                    && ltq!(m_, -1)
                    && integersq!([
                        Atom::num(2) * &m_,
                        Atom::num(2) * &n_,
                        Atom::num(2) * &p_
                    ])
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &m1 * (&b__ * &c__ - &a__ * &d__) * (&b__ * &e__ - &a__ * &f__);
            let simp = simp!(
                &a__ * &d__ * &f__ * &m1
                    - &b__
                        * (&d__ * &e__ * (&m_ + &n_ + Atom::num(2))
                            + &c__ * &f__ * (&m_ + &p_ + Atom::num(2)))
                    - &b__ * &d__ * &f__ * (&m_ + &n_ + &p_ + Atom::num(3)) * x_,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(&n_) * third.pow(&p_) * simp),
                x_,
            );
            let direct = &b__ * first.pow(&m1)
                * second.pow(&n_ + Atom::num(1))
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 116,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_] :=
          -4 \\[Star] Subst[Int[x^2/((b*e-a*f-b*x^4)*Sqrt[c-d*e/f+d*x^4/f]),x],x,(e+f*x)^(1/4)] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[-f/(d*e-c*f),0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(-&f__ / (&d__ * &e__ - &c__ * &f__), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let sub4 = sub.pow(4);
            let transformed_integrand = sub.pow(2)
                / ((&b__ * &e__ - &a__ * &f__ - &b__ * &sub4)
                    * (&c__ - &d__ * &e__ / &f__ + &d__ * sub4 / &f__).sqrt());
            let transformed_primitive =
                rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = substitute_symbol(
                &transformed_primitive,
                sub_symbol,
                (&e__ + &f__ * x_).pow(Atom::num(1) / Atom::num(4)),
            );
            rubi_star(Atom::num(-4), substituted)
        },
    ));
}

fn push_rules_rule_117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 117,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_] :=
          Sqrt[-f*(c+d*x)/(d*e-c*f)]/Sqrt[c+d*x] \\[Star] Int[1/((a+b*x)*Sqrt[-c*f/(d*e-c*f)-d*f*x/(d*e-c*f)]*(e+f*x)^(1/4)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[-f/(d*e-c*f),0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !gtq!(-&f__ / (&d__ * &e__ - &c__ * &f__), 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let cross = &d__ * &e__ - &c__ * &f__;
            let transformed_radical =
                (-&c__ * &f__ / &cross - &d__ * &f__ * x_ / &cross).sqrt();
            let rest = rubi_rhs_int(
                &(Atom::num(1)
                    / (first
                        * transformed_radical
                        * third.pow(Atom::num(1) / Atom::num(4)))),
                x_,
            );
            rubi_star((-&f__ * &second / &cross).sqrt() / second.sqrt(), rest)
        },
    ));
}

fn push_rules_rule_118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 118,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_] :=
          -4 \\[Star] Subst[Int[1/((b*e-a*f-b*x^4)*Sqrt[c-d*e/f+d*x^4/f]),x],x,(e+f*x)^(1/4)] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[-f/(d*e-c*f),0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(-&f__ / (&d__ * &e__ - &c__ * &f__), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let sub4 = sub.pow(4);
            let transformed_integrand = Atom::num(1)
                / ((&b__ * &e__ - &a__ * &f__ - &b__ * &sub4)
                    * (&c__ - &d__ * &e__ / &f__ + &d__ * sub4 / &f__).sqrt());
            let transformed_primitive =
                rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = substitute_symbol(
                &transformed_primitive,
                sub_symbol,
                (&e__ + &f__ * x_).pow(Atom::num(1) / Atom::num(4)),
            );
            rubi_star(Atom::num(-4), substituted)
        },
    ));
}

fn push_rules_rule_119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 119,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_] :=
          Sqrt[-f*(c+d*x)/(d*e-c*f)]/Sqrt[c+d*x] \\[Star] Int[1/((a+b*x)*Sqrt[-c*f/(d*e-c*f)-d*f*x/(d*e-c*f)]*(e+f*x)^(3/4)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[-f/(d*e-c*f),0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !gtq!(-&f__ / (&d__ * &e__ - &c__ * &f__), 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let cross = &d__ * &e__ - &c__ * &f__;
            let transformed_radical =
                (-&c__ * &f__ / &cross - &d__ * &f__ * x_ / &cross).sqrt();
            let rest = rubi_rhs_int(
                &(Atom::num(1)
                    / (first
                        * transformed_radical
                        * third.pow(Atom::num(3) / Atom::num(4)))),
                x_,
            );
            rubi_star((-&f__ * &second / &cross).sqrt() / second.sqrt(), rest)
        },
    ));
}

fn push_rules_rule_120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 120,
        source: "Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_] :=
          2*Sqrt[e]/b*Rt[-b/d,2]*EllipticE[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && Not[LtQ[-b/d,0]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
                && !ltq!((-&b__ / &d__), 0)
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ / &d__), 2);
            rubi_simp(&(Atom::num(2) * e__.sqrt() / &b__
                    * &rt
                    * rubi_elliptic_e(
                        ((&b__ * x_).sqrt() / (c__.sqrt() * &rt)).asin(),
                        &c__ * &f__ / (&d__ * &e__),
                    )), x_)
        },
    ));
}

fn push_rules_rule_121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 121,
        source: "Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_] :=
          Sqrt[-b*x]/Sqrt[b*x] \\[Star] Int[Sqrt[e+f*x]/(Sqrt[-b*x]*Sqrt[c+d*x]),x] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && LtQ[-b/d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
                && ltq!((-&b__ / &d__), 0)
        },
        rhs: {
            let rest = rubi_rhs_int(
                &((&e__ + &f__ * x_).sqrt()
                    / ((-&b__ * x_).sqrt() * (&c__ + &d__ * x_).sqrt())),
                x_,
            );
            rubi_star((-&b__ * x_).sqrt() / (&b__ * x_).sqrt(), rest)
        },
    ));
}

fn push_rules_rule_122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 122,
        source: "Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_] :=
          Sqrt[e+f*x]*Sqrt[1+d*x/c]/(Sqrt[c+d*x]*Sqrt[1+f*x/e]) \\[Star] Int[Sqrt[1+f*x/e]/(Sqrt[b*x]*Sqrt[1+d*x/c]),x] /;
        FreeQ[{b,c,d,e,f},x] && Not[GtQ[c,0] && GtQ[e,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && !(gtq!(c__, 0) && gtq!(e__, 0))
        },
        rhs: {
            let rest = rubi_rhs_int(
                &((Atom::num(1) + &f__ * x_ / &e__).sqrt()
                    / ((&b__ * x_).sqrt()
                        * (Atom::num(1) + &d__ * x_ / &c__).sqrt())),
                x_,
            );
            let multiplier = (&e__ + &f__ * x_).sqrt()
                * (Atom::num(1) + &d__ * x_ / &c__).sqrt()
                / ((&c__ + &d__ * x_).sqrt()
                    * (Atom::num(1) + &f__ * x_ / &e__).sqrt());
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 123,
        source: "Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_] :=
          2/b*Rt[-(b*e-a*f)/d,2]*EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && Not[LtQ[-(b*c-a*d)/d,0]] &&
          Not[SimplerQ[c+d*x,a+b*x] && GtQ[-d/(b*c-a*d),0] && GtQ[d/(d*e-c*f),0] && Not[LtQ[(b*c-a*d)/b,0]]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(&b__ / (&b__ * &c__ - &a__ * &d__), 0)
                && gtq!(&b__ / (&b__ * &e__ - &a__ * &f__), 0)
                && !ltq!((-(&b__ * &c__ - &a__ * &d__) / &d__), 0)
                && !(simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_)
                    && gtq!(-&d__ / (&b__ * &c__ - &a__ * &d__), 0)
                    && gtq!(&d__ / (&d__ * &e__ - &c__ * &f__), 0)
                    && !ltq!((&b__ * &c__ - &a__ * &d__) / &b__, 0))
        },
        rhs: {
            let first_second = &b__ * &c__ - &a__ * &d__;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let rt_first_third = rubi_rt(&(-&first_third / &d__), 2);
            let rt_first_second = rubi_rt(&(-&first_second / &d__), 2);
            rubi_simp(&(Atom::num(2) / &b__
                    * rt_first_third
                    * rubi_elliptic_e(
                        ((&a__ + &b__ * x_).sqrt() / rt_first_second).asin(),
                        &f__ * first_second / (&d__ * first_third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 124,
        source: "Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_] :=
          Sqrt[e+f*x]*Sqrt[b*(c+d*x)/(b*c-a*d)]/(Sqrt[c+d*x]*Sqrt[b*(e+f*x)/(b*e-a*f)]) \\[Star]
            Int[Sqrt[b*e/(b*e-a*f)+b*f*x/(b*e-a*f)]/(Sqrt[a+b*x]*Sqrt[b*c/(b*c-a*d)+b*d*x/(b*c-a*d)]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0]] && Not[LtQ[-(b*c-a*d)/d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !(gtq!(&b__ / (&b__ * &c__ - &a__ * &d__), 0)
                    && gtq!(&b__ / (&b__ * &e__ - &a__ * &f__), 0))
                && !ltq!((-(&b__ * &c__ - &a__ * &d__) / &d__), 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let first_second = &b__ * &c__ - &a__ * &d__;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let normalized_second =
                &b__ * &c__ / &first_second + &b__ * &d__ * x_ / &first_second;
            let normalized_third =
                &b__ * &e__ / &first_third + &b__ * &f__ * x_ / &first_third;
            let rest = rubi_rhs_int(
                &(normalized_third.sqrt() / (first.sqrt() * normalized_second.sqrt())),
                x_,
            );
            let multiplier = third.sqrt() * (&b__ * &second / &first_second).sqrt()
                / (second.sqrt() * (&b__ * &third / &first_third).sqrt());
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 125,
        source: "Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          2/(b*Sqrt[e])*Rt[-b/d,2]*EllipticF[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && (GtQ[-b/d,0] || LtQ[-b/f,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
                && (gtq!(-&b__ / &d__, 0) || ltq!((-&b__ / &f__), 0))
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ / &d__), 2);
            rubi_simp(&(Atom::num(2) / (&b__ * e__.sqrt())
                    * &rt
                    * rubi_elliptic_f(
                        ((&b__ * x_).sqrt() / (c__.sqrt() * &rt)).asin(),
                        &c__ * &f__ / (&d__ * &e__),
                    )), x_)
        },
    ));
}

fn push_rules_rule_126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 126,
        source: "Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          2/(b*Sqrt[e])*Rt[-b/d,2]*EllipticF[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && (PosQ[-b/d] || NegQ[-b/f])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
                && (posq!(-&b__ / &d__) || negq!(-&b__ / &f__))
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ / &d__), 2);
            rubi_simp(&(Atom::num(2) / (&b__ * e__.sqrt())
                    * &rt
                    * rubi_elliptic_f(
                        ((&b__ * x_).sqrt() / (c__.sqrt() * &rt)).asin(),
                        &c__ * &f__ / (&d__ * &e__),
                    )), x_)
        },
    ));
}

fn push_rules_rule_127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 127,
        source: "Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          Sqrt[1+d*x/c]*Sqrt[1+f*x/e]/(Sqrt[c+d*x]*Sqrt[e+f*x]) \\[Star] Int[1/(Sqrt[b*x]*Sqrt[1+d*x/c]*Sqrt[1+f*x/e]),x] /;
        FreeQ[{b,c,d,e,f},x] && Not[GtQ[c,0] && GtQ[e,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && !(gtq!(c__, 0) && gtq!(e__, 0))
        },
        rhs: {
            let rest = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&b__ * x_).sqrt()
                        * (Atom::num(1) + &d__ * x_ / &c__).sqrt()
                        * (Atom::num(1) + &f__ * x_ / &e__).sqrt())),
                x_,
            );
            let multiplier = (Atom::num(1) + &d__ * x_ / &c__).sqrt()
                * (Atom::num(1) + &f__ * x_ / &e__).sqrt()
                / ((&c__ + &d__ * x_).sqrt() * (&e__ + &f__ * x_).sqrt());
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 128,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          -2*Sqrt[d/f]/(d*Rt[-(b*e-a*f)/f,2])*EllipticF[ArcSin[Rt[-(b*e-a*f)/f,2]/Sqrt[a+b*x]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[d/b,0] && GtQ[f/b,0] && LeQ[c,a*d/b] && LeQ[e,a*f/b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(&d__ / &b__, 0)
                && gtq!(&f__ / &b__, 0)
                && leq!(c__, &a__ * &d__ / &b__)
                && leq!(e__, &a__ * &f__ / &b__)
        },
        rhs: {
            let first_third = &b__ * &e__ - &a__ * &f__;
            let rt = rubi_rt(&(-&first_third / &f__), 2);
            rubi_simp(&(-Atom::num(2) * (&d__ / &f__).sqrt() / (&d__ * &rt)
                    * rubi_elliptic_f(
                        (&rt / (&a__ + &b__ * x_).sqrt()).asin(),
                        &f__ * (&b__ * &c__ - &a__ * &d__) / (&d__ * first_third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 129,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          2*Rt[-b/d,2]/(b*Sqrt[(b*e-a*f)/b])*EllipticF[ArcSin[Sqrt[a+b*x]/(Rt[-b/d,2]*Sqrt[(b*c-a*d)/b])],f*(b*c-a*d)/(d*(b*e-a*f))] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[(b*c-a*d)/b,0] && GtQ[(b*e-a*f)/b,0] && PosQ[-b/d] &&
          Not[SimplerQ[c+d*x,a+b*x] && GtQ[(d*e-c*f)/d,0] && GtQ[-d/b,0]] &&
          Not[SimplerQ[c+d*x,a+b*x] && GtQ[(-b*e+a*f)/f,0] && GtQ[-f/b,0]] &&
          Not[SimplerQ[e+f*x,a+b*x] && GtQ[(-d*e+c*f)/f,0] && GtQ[(-b*e+a*f)/f,0] && (PosQ[-f/d] || PosQ[-f/b])]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!((&b__ * &c__ - &a__ * &d__) / &b__, 0)
                && gtq!((&b__ * &e__ - &a__ * &f__) / &b__, 0)
                && posq!(-&b__ / &d__)
                && !(simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_)
                    && gtq!((&d__ * &e__ - &c__ * &f__) / &d__, 0)
                    && gtq!(-&d__ / &b__, 0))
                && !(simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_)
                    && gtq!((-&b__ * &e__ + &a__ * &f__) / &f__, 0)
                    && gtq!(-&f__ / &b__, 0))
                && !(simplerq!(&e__ + &f__ * x_, &a__ + &b__ * x_)
                    && gtq!((-&d__ * &e__ + &c__ * &f__) / &f__, 0)
                    && gtq!((-&b__ * &e__ + &a__ * &f__) / &f__, 0)
                    && (posq!(-&f__ / &d__) || posq!(-&f__ / &b__)))
        },
        rhs: {
            let first_second = &b__ * &c__ - &a__ * &d__;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let rt = rubi_rt(&(-&b__ / &d__), 2);
            rubi_simp(&(Atom::num(2) * &rt / (&b__ * (&first_third / &b__).sqrt())
                    * rubi_elliptic_f(
                        ((&a__ + &b__ * x_).sqrt() / (&rt * (&first_second / &b__).sqrt())).asin(),
                        &f__ * first_second / (&d__ * first_third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 130,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          2*Rt[-b/d,2]/(b*Sqrt[(b*e-a*f)/b])*EllipticF[ArcSin[Sqrt[a+b*x]/(Rt[-b/d,2]*Sqrt[(b*c-a*d)/b])],f*(b*c-a*d)/(d*(b*e-a*f))] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x] &&
          (PosQ[-(b*c-a*d)/d] || NegQ[-(b*e-a*f)/f]) (* && PosQ[-b/d] *)",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(&b__ / (&b__ * &c__ - &a__ * &d__), 0)
                && gtq!(&b__ / (&b__ * &e__ - &a__ * &f__), 0)
                && simplerq!(&a__ + &b__ * x_, &c__ + &d__ * x_)
                && simplerq!(&a__ + &b__ * x_, &e__ + &f__ * x_)
                && (posq!(-(&b__ * &c__ - &a__ * &d__) / &d__)
                    || negq!(-(&b__ * &e__ - &a__ * &f__) / &f__))
        },
        rhs: {
            let first_second = &b__ * &c__ - &a__ * &d__;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let rt = rubi_rt(&(-&b__ / &d__), 2);
            rubi_simp(&(Atom::num(2) * &rt / (&b__ * (&first_third / &b__).sqrt())
                    * rubi_elliptic_f(
                        ((&a__ + &b__ * x_).sqrt() / (&rt * (&first_second / &b__).sqrt())).asin(),
                        &f__ * first_second / (&d__ * first_third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 131,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          Sqrt[b*(c+d*x)/(b*c-a*d)]/Sqrt[c+d*x] \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[b*c/(b*c-a*d)+b*d*x/(b*c-a*d)]*Sqrt[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[(b*c-a*d)/b,0]] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !gtq!((&b__ * &c__ - &a__ * &d__) / &b__, 0)
                && simplerq!(&a__ + &b__ * x_, &c__ + &d__ * x_)
                && simplerq!(&a__ + &b__ * x_, &e__ + &f__ * x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let first_second = &b__ * &c__ - &a__ * &d__;
            let normalized_second =
                &b__ * &c__ / &first_second + &b__ * &d__ * x_ / &first_second;
            let rest = rubi_rhs_int(
                &(Atom::num(1)
                    / (first.sqrt() * normalized_second.sqrt() * third.sqrt())),
                x_,
            );
            let multiplier = (&b__ * &second / &first_second).sqrt() / second.sqrt();
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 132,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
          Sqrt[b*(e+f*x)/(b*e-a*f)]/Sqrt[e+f*x] \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[b*e/(b*e-a*f)+b*f*x/(b*e-a*f)]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[(b*e-a*f)/b,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !gtq!((&b__ * &e__ - &a__ * &f__) / &b__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let normalized_third =
                &b__ * &e__ / &first_third + &b__ * &f__ * x_ / &first_third;
            let rest = rubi_rhs_int(
                &(Atom::num(1)
                    / (first.sqrt() * second.sqrt() * normalized_third.sqrt())),
                x_,
            );
            let multiplier = (&b__ * &third / &first_third).sqrt() / third.sqrt();
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 133,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(1/3)),x_] :=
          With[{q=Rt[b*(b*e-a*f)/(b*c-a*d)^2,3]},
          -Log[a+b*x]/(2*q*(b*c-a*d)) -
          Sqrt[3]*ArcTan[1/Sqrt[3]+2*q*(c+d*x)^(2/3)/(Sqrt[3]*(e+f*x)^(1/3))]/(2*q*(b*c-a*d)) +
          3*Log[q*(c+d*x)^(2/3)-(e+f*x)^(1/3)]/(4*q*(b*c-a*d))] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-b*c*f-a*d*f,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_)
                * (c__ + d__ * x_).pow((1, 3))
                * (e__ + f__ * x_).pow((1, 3))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(Atom::num(2) * &b__ * &d__ * &e__ - &b__ * &c__ * &f__ - &a__ * &d__ * &f__, Atom::num(0))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let cross = &b__ * &c__ - &a__ * &d__;
            let q = rubi_rt(&(&b__ * (&b__ * &e__ - &a__ * &f__) / cross.pow(2)), 3);
            let sqrt3 = Atom::num(3).sqrt();
            rubi_simp(&(-first.log() / (Atom::num(2) * &q * &cross)), x_)
                    - rubi_simp(&(&sqrt3
                        * (Atom::num(1) / &sqrt3
                            + Atom::num(2) * &q * second.pow(Atom::num(2) / Atom::num(3))
                                / (&sqrt3 * third.pow(Atom::num(1) / Atom::num(3))))
                        .atan()
                        / (Atom::num(2) * &q * &cross)), x_)
                    + rubi_simp(&(Atom::num(3)
                        * (&q * second.pow(Atom::num(2) / Atom::num(3))
                            - third.pow(Atom::num(1) / Atom::num(3)))
                        .log()
                        / (Atom::num(4) * q * cross)), x_)
        },
    ));
}

fn push_rules_rule_134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 134,
        source: "Int[(a_.+b_.*x_)^m_/((c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(1/3)),x_] :=
          b*(a+b*x)^(m+1)*(c+d*x)^(2/3)*(e+f*x)^(2/3)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          f/(6*(m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star]
            Int[(a+b*x)^(m+1)*(a*d*(3*m+1)-3*b*c*(3*m+5)-2*b*d*(3*m+7)*x)/((c+d*x)^(1/3)*(e+f*x)^(1/3)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-b*c*f-a*d*f,0] && ILtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_)
            / ((c__ + d__ * x_).pow((1, 3)) * (e__ + f__ * x_).pow((1, 3))),
        with: [a__, b__, c__, d__, e__, f__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(Atom::num(2) * &b__ * &d__ * &e__ - &b__ * &c__ * &f__ - &a__ * &d__ * &f__, Atom::num(0))
                && iltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ + Atom::num(1);
            let cross_second = &b__ * &c__ - &a__ * &d__;
            let cross_third = &b__ * &e__ - &a__ * &f__;
            let denominator = &m1 * &cross_second * &cross_third;
            let linear = &a__ * &d__ * (Atom::num(3) * &m_ + Atom::num(1))
                - Atom::num(3) * &b__ * &c__ * (Atom::num(3) * &m_ + Atom::num(5))
                - Atom::num(2) * &b__ * &d__ * (Atom::num(3) * &m_ + Atom::num(7)) * x_;
            let direct = &b__ * first.pow(&m1)
                * second.pow(Atom::num(2) / Atom::num(3))
                * third.pow(Atom::num(2) / Atom::num(3))
                / &denominator;
            let rest = rubi_rhs_int(
                &(first.pow(m1)
                    * linear
                    / (second.pow(Atom::num(1) / Atom::num(3))
                        * third.pow(Atom::num(1) / Atom::num(3)))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&f__ / (Atom::num(6) * denominator), rest)
        },
    ));
}

fn push_rules_rule_135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, f__);
    rules.push(rubi_rule!(
        order: 135,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(f_.*x_)^p_,x_] :=
          Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
        FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[n,m] && GtQ[a,0] && GtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(n_, m_)
                && gtq!(a__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            rubi_rhs_int(&((&a__ * &c__ + &b__ * &d__ * x_.pow(2)).pow(m_) * (&f__ * x_).pow(p_)), x_)
        },
    ));
}

fn push_rules_rule_136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, f__);
    rules.push(rubi_rule!(
        order: 136,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(f_.*x_)^p_,x_] :=
          (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m] \\[Star] Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
        FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[n,m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(n_, m_)
        },
        rhs: {
            let frac = rubi_frac_part(&m_);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let rest = rubi_rhs_int(&(quadratic.pow(m_) * (&f__ * x_).pow(p_)), x_);
            let multiplier = first.pow(&frac) * second.pow(&frac) / quadratic.pow(frac);
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 137,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && (IGtQ[m,0] || ILtQ[m,0] && ILtQ[n,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && (igtq!(m_, 0) || iltq!(m_, 0) && iltq!(n_, 0))
        },
        rhs: {
            let integrand =
                (&a__ + &b__ * x_).pow(m_) * (&c__ + &d__ * x_).pow(n_) * (&e__ + &f__ * x_).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 148,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_] :=
          With[{k=Denominator[m]},
          k/b \\[Star] Subst[Int[x^(k*(m+1)-1)*(c+d*x^k/b)^n*(e+f*x^k/b)^p,x],x,(b*x)^(1/k)]] /;
        FreeQ[{b,c,d,e,f,n,p},x] && FractionQ[m] && IntegerQ[p]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, f__, n_, p_],
        x_free: [b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([b__, c__, d__, e__, f__, n_, p_], x_)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let k = Atom::num(denominator!(m_));
            let sub_k = sub.pow(&k);
            let transformed_integrand = sub.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&c__ + &d__ * &sub_k / &b__).pow(n_)
                * (&e__ + &f__ * sub_k / &b__).pow(p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = substitute_symbol(
                &transformed_primitive,
                sub_symbol,
                (&b__ * x_).pow(Atom::num(1) / &k),
            );
            rubi_star(&k / &b__, substituted)
        },
    ));
}

fn push_rules_rule_149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 149,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_] :=
          With[{k=Denominator[m]},
          k/b \\[Star] Subst[Int[x^(k*(m+1)-1)*(c-a*d/b+d*x^k/b)^n*(e-a*f/b+f*x^k/b)^p,x],x,(a+b*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && FractionQ[m] && IntegerQ[2*n] && IntegerQ[p]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && fractionq!(m_)
                && integerq!(Atom::num(2) * &n_)
                && integerq!(p_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let k = Atom::num(denominator!(m_));
            let sub_k = sub.pow(&k);
            let transformed_integrand = sub.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&c__ - &a__ * &d__ / &b__ + &d__ * &sub_k / &b__).pow(n_)
                * (&e__ - &a__ * &f__ / &b__ + &f__ * sub_k / &b__).pow(p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = substitute_symbol(
                &transformed_primitive,
                sub_symbol,
                (&a__ + &b__ * x_).pow(Atom::num(1) / &k),
            );
            rubi_star(&k / &b__, substituted)
        },
    ));
}

fn push_rules_rule_138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 138,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_)^2,x_] :=
          b*d/f^2 \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^(n-1),x] +
          (b*e-a*f)*(d*e-c*f)/f^2 \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^(n-1)/(e+f*x)^2,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[m+n,0] && EqQ[2*b*d*e-f*(b*c+a*d),0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) / (e__ + f__ * x_).pow(2),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && igtq!(&m_ + &n_, 0)
                && eqq!(Atom::num(2) * &b__ * &d__ * &e__ - &f__ * (&b__ * &c__ + &a__ * &d__), Atom::num(0))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let lowered = first.pow(&m_ - Atom::num(1)) * second.pow(&n_ - Atom::num(1));
            let first_rest = rubi_rhs_int(&lowered, x_);
            let second_rest = rubi_rhs_int(&(lowered / third.pow(2)), x_);
            rubi_star(&b__ * &d__ / f__.pow(2), first_rest)
                    + rubi_star((&b__ * &e__ - &a__ * &f__)
                            * (&d__ * &e__ - &c__ * &f__)
                            / f__.pow(2), second_rest)
        },
    ));
}

fn push_rules_rule_139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 139,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          f^(p-1)/d^p \\[Star] Int[(a+b*x)^m*(d*e*p-c*f*(p-1)+d*f*x)/(c+d*x)^(m+1),x] +
          f^(p-1) \\[Star] Int[(a+b*x)^m*(e+f*x)^p/(c+d*x)^(m+1)*
            ExpandToSum[f^(-p+1)*(c+d*x)^(-p+1)-(d*e*p-c*f*(p-1)+d*f*x)/(d^p*(e+f*x)^p),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[m+n+p,0] && ILtQ[p,0] && (LtQ[m,0] || SumSimplerQ[m,1] || Not[LtQ[n,0] || SumSimplerQ[n,1]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ + &p_, Atom::num(0))
                && iltq!(p_, 0)
                && (ltq!(m_, 0)
                    || sum_simplerq!(m_, 1)
                    || !(ltq!(n_, 0) || sum_simplerq!(n_, 1)))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let linear = &d__ * &e__ * &p_ - &c__ * &f__ * (&p_ - Atom::num(1)) + &d__ * &f__ * x_;
            let expand_to_sum = f__.pow(-&p_ + Atom::num(1))
                * second.pow(-&p_ + Atom::num(1))
                - &linear / (d__.pow(&p_) * third.pow(&p_));
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum, x_);
            let first_rest = rubi_rhs_int(
                &(first.pow(&m_) * &linear / second.pow(&m_ + Atom::num(1))),
                x_,
            );
            let second_rest = rubi_rhs_int(
                        &(first.pow(&m_) * third.pow(&p_) * expand_to_sum
                    / second.pow(&m_ + Atom::num(1))),
                x_,
            );
            rubi_star(f__.pow(&p_ - Atom::num(1)) / d__.pow(&p_), first_rest) + rubi_star(f__.pow(&p_ - Atom::num(1)), second_rest)
        },
    ));
}

fn push_rules_rule_140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 140,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          b*d^(m+n)*f^p \\[Star] Int[(a+b*x)^(m-1)/(c+d*x)^m,x] +
          Int[(a+b*x)^(m-1)*(e+f*x)^p/(c+d*x)^m*ExpandToSum[(a+b*x)*(c+d*x)^(-p-1)-(b*d^(-p-1)*f^p)/(e+f*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[m+n+p+1,0] && ILtQ[p,0] && (GtQ[m,0] || SumSimplerQ[m,-1] || Not[GtQ[n,0] || SumSimplerQ[n,-1]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ + &p_ + Atom::num(1), Atom::num(0))
                && iltq!(p_, 0)
                && (gtq!(m_, 0)
                    || sum_simplerq!(m_, -1)
                    || !(gtq!(n_, 0) || sum_simplerq!(n_, -1)))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let expand_to_sum = &first * second.pow(-&p_ - Atom::num(1))
                - &b__ * d__.pow(-&p_ - Atom::num(1)) * f__.pow(&p_) / third.pow(&p_);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum, x_);
            let first_rest = rubi_rhs_int(
                &(first.pow(&m_ - Atom::num(1)) / second.pow(&m_)),
                x_,
            );
            let second_rest = rubi_rhs_int(
                &(first.pow(&m_ - Atom::num(1)) * third.pow(&p_) * expand_to_sum
                    / second.pow(&m_)),
                x_,
            );
            rubi_star(&b__ * d__.pow(&m_ + &n_) * f__.pow(&p_), first_rest) + second_rest
        },
    ));
}

fn push_rules_rule_141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 141,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (b*c-a*d)^n*(a+b*x)^(m+1)/((m+1)*(b*e-a*f)^(n+1)*(e+f*x)^(m+1))*
            Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[m+n+p+2,0] && ILtQ[n,0] && (SumSimplerQ[m,1] || Not[SumSimplerQ[p,1]]) && Not[ILtQ[m,0]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
                && iltq!(n_, 0)
                && (sum_simplerq!(m_, 1) || !sum_simplerq!(p_, 1))
                && !iltq!(m_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let third = &e__ + &f__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            rubi_simp(&(bc_ad.pow(&n_) * first.pow(&m_ + Atom::num(1))
                    / ((&m_ + Atom::num(1))
                        * be_af.pow(&n_ + Atom::num(1))
                        * third.pow(&m_ + Atom::num(1)))
                    * rubi_hypergeometric2f1(
                        &m_ + Atom::num(1),
                        -&n_,
                        &m_ + Atom::num(2),
                        -(&d__ * &e__ - &c__ * &f__) * first / (bc_ad * third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 142,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((b*e-a*f)*(m+1))*((b*e-a*f)*(c+d*x)/((b*c-a*d)*(e+f*x)))^(-n)*
            Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[m+n+p+2,0] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
                && !integerq!(n_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            rubi_simp(&(first.pow(&m_ + Atom::num(1))
                    * second.pow(&n_)
                    * third.pow(&p_ + Atom::num(1))
                    / (&be_af * (&m_ + Atom::num(1)))
                    * ((&be_af * second) / (&bc_ad * &third)).pow(-&n_)
                    * rubi_hypergeometric2f1(
                        &m_ + Atom::num(1),
                        -&n_,
                        &m_ + Atom::num(2),
                        -(&d__ * &e__ - &c__ * &f__) * first / (bc_ad * third),
                    )), x_)
        },
    ));
}

fn push_rules_rule_143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 143,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_] :=
          (c*f-d*e)^(m+n+1)/f^(m+n+1) \\[Star] Int[(a+b*x)^m/((c+d*x)^(m+1)*(e+f*x)),x] +
          1/f^(m+n+1) \\[Star] Int[(a+b*x)^m/(c+d*x)^(m+1)*ExpandToSum[(f^(m+n+1)*(c+d*x)^(m+n+1)-(c*f-d*e)^(m+n+1))/(e+f*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[m+n+1,0] && (LtQ[m,0] || SumSimplerQ[m,1] || Not[LtQ[n,0] || SumSimplerQ[n,1]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) / (e__ + f__ * x_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && igtq!(&m_ + &n_ + Atom::num(1), 0)
                && (ltq!(m_, 0)
                    || sum_simplerq!(m_, 1)
                    || !(ltq!(n_, 0) || sum_simplerq!(n_, 1)))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let q = &m_ + &n_ + Atom::num(1);
            let cf_de = &c__ * &f__ - &d__ * &e__;
            let expand_to_sum =
                (f__.pow(&q) * second.pow(&q) - cf_de.pow(&q)) / &third;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum, x_);
            let first_rest = rubi_rhs_int(
                &(first.pow(&m_)
                    / (second.pow(&m_ + Atom::num(1)) * &third)),
                x_,
            );
            let second_rest = rubi_rhs_int(
                &(first.pow(&m_) / second.pow(&m_ + Atom::num(1)) * expand_to_sum),
                x_,
            );
            rubi_star(cf_de.pow(&q) / f__.pow(&q), first_rest)
                    + rubi_star(Atom::num(1) / f__.pow(&q), second_rest)
        },
    ));
}

fn push_rules_rule_144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 144,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          With[{mnp=Simplify[m+n+p]},
          b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(mnp+3)*x,x],x] /;
         ILtQ[mnp+2,0] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && NeQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            let mnp = rubi_simplify(&(&m_ + &n_ + &p_));
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && iltq!(&mnp + Atom::num(2), 0)
                && neq!(m_, -Atom::num(1))
                && (sum_simplerq!(m_, 1)
                    || !sum_simplerq!(n_, 1) && !sum_simplerq!(p_, 1))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let first_second = &b__ * &c__ - &a__ * &d__;
            let first_third = &b__ * &e__ - &a__ * &f__;
            let denominator = (&m_ + Atom::num(1)) * &first_second * &first_third;
            let mnp = rubi_simplify(&(&m_ + &n_ + &p_));
            let simp = simp!(
                &a__ * &d__ * &f__ * (&m_ + Atom::num(1))
                    - &b__
                        * (&d__ * &e__ * (&m_ + &n_ + Atom::num(2))
                            + &c__ * &f__ * (&m_ + &p_ + Atom::num(2)))
                    - &b__ * &d__ * &f__ * (&mnp + Atom::num(3)) * x_,
                x_
            );
            let direct = &b__ * first.pow(&m_ + Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * third.pow(&p_ + Atom::num(1))
                / &denominator;
            let rest = rubi_rhs_int(
                &(first.pow(&m_ + Atom::num(1))
                    * second.pow(n_)
                    * third.pow(p_)
                    * simp),
                x_,
            );
            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / denominator, rest)
        },
    ));
}

fn push_rules_rule_145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 145,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          1/b \\[Star] Subst[Int[x^m*(c*e-(d*e+c*f)^2/(4*d*f)+d*f*x^2/b^2)^n,x],x,a+b*x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[p,n] && EqQ[b*d*e+b*c*f-2*a*d*f,0] && EqQ[d*e+c*f,0] && GtQ[c,0] && GtQ[e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(p_, n_)
                && eqq!(&b__ * &d__ * &e__ + &b__ * &c__ * &f__ - Atom::num(2) * &a__ * &d__ * &f__, 0)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let quadratic = &c__ * &e__
                - (&d__ * &e__ + &c__ * &f__).pow(2)
                    / (Atom::num(4) * &d__ * &f__)
                + &d__ * &f__ * sub.pow(2) / b__.pow(2);
            let transformed_primitive =
                rubi_rhs_int(&(sub.pow(&m_) * quadratic.pow(&n_)), sub_symbol);
            let substituted =
                substitute_symbol(&transformed_primitive, sub_symbol, &a__ + &b__ * x_);
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 146,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (c+d*x)^n*(e+f*x)^p/(b*(c*e+(d*e+c*f)*x+d*f*x^2)^n) \\[Star]
            Subst[Int[x^m*(c*e-(d*e+c*f)^2/(4*d*f)+d*f*x^2/b^2)^n,x],x,a+b*x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[p,n] && EqQ[b*d*e+b*c*f-2*a*d*f,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(p_, n_)
                && eqq!(&b__ * &d__ * &e__ + &b__ * &c__ * &f__ - Atom::num(2) * &a__ * &d__ * &f__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let quadratic = &c__ * &e__
                - (&d__ * &e__ + &c__ * &f__).pow(2)
                    / (Atom::num(4) * &d__ * &f__)
                + &d__ * &f__ * sub.pow(2) / b__.pow(2);
            let transformed_primitive =
                rubi_rhs_int(&(sub.pow(&m_) * quadratic.pow(&n_)), sub_symbol);
            let substituted =
                substitute_symbol(&transformed_primitive, sub_symbol, &a__ + &b__ * x_);
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let denominator = &b__
                * (&c__ * &e__
                    + (&d__ * &e__ + &c__ * &f__) * x_
                    + &d__ * &f__ * x_.pow(2))
                .pow(&n_);
            let multiplier = second.pow(&n_) * third.pow(&p_) / denominator;
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, f__);
    rules.push(rubi_rule!(
        order: 147,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(f_.*x_)^p_,x_] :=
          Int[ExpandIntegrand[(a+b*x)^n*(c+d*x)^n*(f*x)^p,(a+b*x)^(m-n),x],x] /;
        FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && IGtQ[m-n,0] && NeQ[m+n+p+2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && igtq!(&m_ - &n_, 0)
                && neq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let scaled = &f__ * x_;
            let expanded = rubi_expand_integrand_product(
                &(first.pow(&n_) * second.pow(&n_) * scaled.pow(p_)),
                &first.pow(&m_ - &n_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 150,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_] :=
          c^n*e^p*(b*x)^(m+1)/(b*(m+1))*AppellF1[m+1,-n,-p,m+2,-d*x/c,-f*x/e] /;
        FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[c,0] && (IntegerQ[p] || GtQ[e,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(c__, 0)
                && (integerq!(p_) || gtq!(e__, 0))
        },
        rhs: {
            rubi_simp(&(c__.pow(&n_) * e__.pow(&p_) * (&b__ * x_).pow(&m_ + Atom::num(1))
                    / (&b__ * (&m_ + Atom::num(1)))
                    * rubi_appell_f1(
                        &m_ + Atom::num(1),
                        -&n_,
                        -&p_,
                        &m_ + Atom::num(2),
                        -&d__ * x_ / &c__,
                        -&f__ * x_ / &e__,
                    )), x_)
        },
    ));
}

fn push_rules_rule_151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 151,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_] :=
          (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m*(d/(d*e-c*f))^p)*AppellF1[n+1,-m,-p,n+2,1+d*x/c,-f*(c+d*x)/(d*e-c*f)] /;
        FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[-d/(b*c),0] && (IntegerQ[p] || GtQ[d/(d*e-c*f),0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(-&d__ / (&b__ * &c__), 0)
                && (integerq!(p_) || gtq!(&d__ / (&d__ * &e__ - &c__ * &f__), 0))
        },
        rhs: {
            let second = &c__ + &d__ * x_;
            let de_cf = &d__ * &e__ - &c__ * &f__;
            rubi_simp(&(second.pow(&n_ + Atom::num(1))
                    / (&d__
                        * (&n_ + Atom::num(1))
                        * (-&d__ / (&b__ * &c__)).pow(&m_)
                        * (&d__ / &de_cf).pow(&p_))
                    * rubi_appell_f1(
                        &n_ + Atom::num(1),
                        -&m_,
                        -&p_,
                        &n_ + Atom::num(2),
                        Atom::num(1) + &d__ * x_ / &c__,
                        -&f__ * second / de_cf,
                    )), x_)
        },
    ));
}

fn push_rules_rule_152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 152,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_] :=
          c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n] \\[Star] Int[(b*x)^m*(1+d*x/c)^n*(e+f*x)^p,x] /;
        FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !gtq!(c__, 0)
        },
        rhs: {
            let second = &c__ + &d__ * x_;
            let normalized_second = Atom::num(1) + &d__ * x_ / &c__;
            let third = &e__ + &f__ * x_;
            let int_part = rubi_int_part(&n_);
            let frac_part = rubi_frac_part(&n_);
            let rest = rubi_rhs_int(
                &((&b__ * x_).pow(m_) * normalized_second.pow(n_) * third.pow(p_)),
                x_,
            );
            let multiplier =
                c__.pow(int_part) * second.pow(&frac_part) / normalized_second.pow(&frac_part);
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 153,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (b*e-a*f)^p*(a+b*x)^(m+1)/(b^(p+1)*(m+1)*Simplify[b/(b*c-a*d)]^n)*
            AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && GtQ[Simplify[b/(b*c-a*d)],0] &&
          Not[GtQ[Simplify[d/(d*a-c*b)],0] && SimplerQ[c+d*x,a+b*x]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && integerq!(p_)
                && gtq!(rubi_simplify(&(&b__ / (&b__ * &c__ - &a__ * &d__))), 0)
                && !(gtq!(rubi_simplify(&(&d__ / (&d__ * &a__ - &c__ * &b__))), 0)
                    && simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let normalized_second = rubi_simplify(&(&b__ / &bc_ad));
            rubi_simp(&(be_af.pow(&p_) * first.pow(&m_ + Atom::num(1))
                    / (b__.pow(&p_ + Atom::num(1))
                        * (&m_ + Atom::num(1))
                        * normalized_second.pow(&n_))
                    * rubi_appell_f1(
                        &m_ + Atom::num(1),
                        -&n_,
                        -&p_,
                        &m_ + Atom::num(2),
                        -&d__ * &first / bc_ad,
                        -&f__ * first / be_af,
                    )), x_)
        },
    ));
}

fn push_rules_rule_154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 154,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (c+d*x)^FracPart[n]/(Simplify[b/(b*c-a*d)]^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n]) \\[Star]
            Int[(a+b*x)^m*Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]^n*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && Not[GtQ[Simplify[b/(b*c-a*d)],0]] &&
          Not[SimplerQ[c+d*x,a+b*x]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && integerq!(p_)
                && !gtq!(rubi_simplify(&(&b__ / (&b__ * &c__ - &a__ * &d__))), 0)
                && !simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let int_part = rubi_int_part(&n_);
            let frac_part = rubi_frac_part(&n_);
            let normalized_coefficient = rubi_simplify(&(&b__ / &bc_ad));
            let transformed_second = simp!(
                &b__ * &c__ / &bc_ad + &b__ * &d__ * x_ / &bc_ad,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(m_) * transformed_second.pow(n_) * third.pow(p_)),
                x_,
            );
            let multiplier = second.pow(&frac_part)
                / (normalized_coefficient.pow(int_part)
                    * (&b__ * second / &bc_ad).pow(&frac_part));
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 155,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (a+b*x)^(m+1)/(b*(m+1)*Simplify[b/(b*c-a*d)]^n*Simplify[b/(b*e-a*f)]^p)*
            AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] &&
          GtQ[Simplify[b/(b*c-a*d)],0] && GtQ[Simplify[b/(b*e-a*f)],0] &&
          Not[GtQ[Simplify[d/(d*a-c*b)],0] && GtQ[Simplify[d/(d*e-c*f)],0] && SimplerQ[c+d*x,a+b*x]] &&
          Not[GtQ[Simplify[f/(f*a-e*b)],0] && GtQ[Simplify[f/(f*c-e*d)],0] && SimplerQ[e+f*x,a+b*x]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !integerq!(p_)
                && gtq!(rubi_simplify(&(&b__ / (&b__ * &c__ - &a__ * &d__))), 0)
                && gtq!(rubi_simplify(&(&b__ / (&b__ * &e__ - &a__ * &f__))), 0)
                && !(gtq!(rubi_simplify(&(&d__ / (&d__ * &a__ - &c__ * &b__))), 0)
                    && gtq!(rubi_simplify(&(&d__ / (&d__ * &e__ - &c__ * &f__))), 0)
                    && simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_))
                && !(gtq!(rubi_simplify(&(&f__ / (&f__ * &a__ - &e__ * &b__))), 0)
                    && gtq!(rubi_simplify(&(&f__ / (&f__ * &c__ - &e__ * &d__))), 0)
                    && simplerq!(&e__ + &f__ * x_, &a__ + &b__ * x_))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let normalized_second = rubi_simplify(&(&b__ / &bc_ad));
            let normalized_third = rubi_simplify(&(&b__ / &be_af));
            rubi_simp(&(first.pow(&m_ + Atom::num(1))
                    / (&b__
                        * (&m_ + Atom::num(1))
                        * normalized_second.pow(&n_)
                        * normalized_third.pow(&p_))
                    * rubi_appell_f1(
                        &m_ + Atom::num(1),
                        -&n_,
                        -&p_,
                        &m_ + Atom::num(2),
                        -&d__ * &first / bc_ad,
                        -&f__ * first / be_af,
                    )), x_)
        },
    ));
}

fn push_rules_rule_156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 156,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (e+f*x)^FracPart[p]/(Simplify[b/(b*e-a*f)]^IntPart[p]*(b*(e+f*x)/(b*e-a*f))^FracPart[p]) \\[Star]
            Int[(a+b*x)^m*(c+d*x)^n*Simp[b*e/(b*e-a*f)+b*f*x/(b*e-a*f),x]^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] &&
          GtQ[Simplify[b/(b*c-a*d)],0] && Not[GtQ[Simplify[b/(b*e-a*f)],0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !integerq!(p_)
                && gtq!(rubi_simplify(&(&b__ / (&b__ * &c__ - &a__ * &d__))), 0)
                && !gtq!(rubi_simplify(&(&b__ / (&b__ * &e__ - &a__ * &f__))), 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let int_part = rubi_int_part(&p_);
            let frac_part = rubi_frac_part(&p_);
            let normalized_coefficient = rubi_simplify(&(&b__ / &be_af));
            let transformed_third = simp!(
                &b__ * &e__ / &be_af + &b__ * &f__ * x_ / &be_af,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(m_) * second.pow(n_) * transformed_third.pow(p_)),
                x_,
            );
            let multiplier = third.pow(&frac_part)
                / (normalized_coefficient.pow(int_part)
                    * (&b__ * third / &be_af).pow(&frac_part));
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 157,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_] :=
          (c+d*x)^FracPart[n]/(Simplify[b/(b*c-a*d)]^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n]) \\[Star]
            Int[(a+b*x)^m*Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]^n*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && Not[GtQ[Simplify[b/(b*c-a*d)],0]] &&
          Not[SimplerQ[c+d*x,a+b*x]] && Not[SimplerQ[e+f*x,a+b*x]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !integerq!(p_)
                && !gtq!(rubi_simplify(&(&b__ / (&b__ * &c__ - &a__ * &d__))), 0)
                && !simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_)
                && !simplerq!(&e__ + &f__ * x_, &a__ + &b__ * x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let int_part = rubi_int_part(&n_);
            let frac_part = rubi_frac_part(&n_);
            let normalized_coefficient = rubi_simplify(&(&b__ / &bc_ad));
            let transformed_second = simp!(
                &b__ * &c__ / &bc_ad + &b__ * &d__ * x_ / &bc_ad,
                x_
            );
            let rest = rubi_rhs_int(
                &(first.pow(m_) * transformed_second.pow(n_) * third.pow(p_)),
                x_,
            );
            let multiplier = second.pow(&frac_part)
                / (normalized_coefficient.pow(int_part)
                    * (&b__ * second / &bc_ad).pow(&frac_part));
            rubi_star(multiplier, rest)
        },
    ));
}

fn push_rules_rule_158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, u_, e__, f__);
    let rule = rubi_rule!(
        order: 158,
        source: "Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.*(e_+f_.*u_)^p_.,x_Symbol] :=
          1/D[u,x] \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u_).pow(m_) * (c__ + d__ * u_).pow(n_) * (e__ + f__ * u_).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, u_, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, f__, m_, n_, p_],
        x_dep: [u_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let Some((_u0, u1)) = linear_coefficients(&u_, x_) else {
                panic!("Rubi RHS invariant was not established by the rule condition");
            };
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &((a__ + b__ * &sub).pow(m_)
                    * (c__ + d__ * &sub).pow(n_)
                    * (e__ + f__ * &sub).pow(p_)),
                sub_symbol,
            );
            let substituted = substitute_symbol(&primitive, sub_symbol, u_);
            rubi_star(Atom::num(1) / u1, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u_)
            .with_repeated_proper_x_dependent_subexpression(),
    );
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_) * (d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(2) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(p_) * (a__ + b__ * x_).pow(-1) * (c__ + d__ * x_).pow(-1)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (e__ + f__ * x_).sqrt() / ((a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (e__ + f__ * x_).sqrt() / ((b__ * x_).sqrt() * (c__ + d__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_) * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).pow((1, 4)))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_) * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).pow((3, 4)))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((b__ * x_).sqrt() * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt())
}
