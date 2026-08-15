use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_159(rules);
    push_rules_rule_160(rules);
    push_rules_rule_161(rules);
    push_rules_rule_162(rules);
    push_rules_rule_163(rules);
    push_rules_rule_164(rules);
    push_rules_rule_165(rules);
    push_rules_rule_166(rules);
    push_rules_rule_167(rules);
    push_rules_rule_168(rules);
    push_rules_rule_169(rules);
    push_rules_rule_170(rules);
    push_rules_rule_171(rules);
    push_rules_rule_172(rules);
    push_rules_rule_173(rules);
    push_rules_rule_174(rules);
    push_rules_rule_175(rules);
    push_rules_rule_176(rules);
    push_rules_rule_177(rules);
    push_rules_rule_178(rules);
    push_rules_rule_179(rules);
    push_rules_rule_180(rules);
    push_rules_rule_181(rules);
    push_rules_rule_182(rules);
    push_rules_rule_183(rules);
    push_rules_rule_184(rules);
    push_rules_rule_185(rules);
    push_rules_rule_186(rules);
    push_rules_rule_187(rules);
    push_rules_rule_188(rules);
    push_rules_rule_189(rules);
    push_rules_rule_190(rules);
    push_rules_rule_191(rules);
    push_rules_rule_192(rules);
    push_rules_rule_193(rules);
    push_rules_rule_194(rules);
    push_rules_rule_195(rules);
    push_rules_rule_196(rules);
    push_rules_rule_197(rules);
    push_rules_rule_198(rules);
    push_rules_rule_199(rules);
    push_rules_rule_200(rules);
    push_rules_rule_201(rules);
    push_rules_rule_202(rules);
}

fn push_rules_rule_159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 159,
        source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)*(g+h*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && (IGtQ[m,0] || IntegersQ[m,n])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
        optional: [a__, b__, c__, d__, f__, g__, h__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && (igtq!(m_, 0) || integersq!([m_, n_]))
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_)
                * (c__ + d__ * x_).pow(n_)
                * (e__ + f__ * x_)
                * (g__ + h__ * x_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    );
    rules.push(rule.with_early_positive_integer_or_integer_pair(m_, n_));
}

fn push_rules_rule_160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 160,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
                  (b^2*d*e*g-a^2*d*f*h*m-a*b*(d*(f*g+e*h)-c*f*h*(m+1))+b*f*h*(b*c-a*d)*(m+1)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
                    (b^2*d*(b*c-a*d)*(m+1)) +
                  (a*d*f*h*m+b*(d*(f*g+e*h)-c*f*h*(m+2)))/(b^2*d) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[m+n+2,0] && NeQ[m,-1] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])",
                desc: "Apply a recurrence relation that reduces the integral.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, f__, g__, h__, n_],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                        && eqq!(&m_ + &n_ + Atom::num(2), Atom::num(0))
                        && neq!(m_, -Atom::num(1))
                        && (sum_simplerq!(m_, 1) || !sum_simplerq!(n_, 1))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let linear = b__.pow(2) * &d__ * &e__ * &g__
                        - a__.pow(2) * &d__ * &f__ * &h__ * &m_
                        - &a__
                            * &b__
                            * (&d__ * (&f__ * &g__ + &e__ * &h__)
                                - &c__ * &f__ * &h__ * (&m_ + Atom::num(1)))
                        + &b__ * &f__ * &h__ * &bc_ad * (&m_ + Atom::num(1)) * x_;
                    let denominator =
                        b__.pow(2) * &d__ * &bc_ad * (&m_ + Atom::num(1));
                    let recurrence_coefficient =
                        (&a__ * &d__ * &f__ * &h__ * &m_
                            + &b__
                                * (&d__ * (&f__ * &g__ + &e__ * &h__)
                                    - &c__ * &f__ * &h__ * (&m_ + Atom::num(2))))
                            / (b__.pow(2) * &d__);
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_ + Atom::num(1)) * second.pow(&n_)),
                        x_,
                    );
                    rubi_simp(&(linear
                            * first.pow(&m_ + Atom::num(1))
                            * second.pow(&n_ + Atom::num(1))
                            / denominator), x_)
                            + rubi_star(recurrence_coefficient, recursive)
                },
            ));
}

fn push_rules_rule_161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 161,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
                  (b^2*c*d*e*g*(n+1)+a^2*c*d*f*h*(n+1)+a*b*(d^2*e*g*(m+1)+c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+n+2))+
                      (a^2*d^2*f*h*(n+1)-a*b*d^2*(f*g+e*h)*(n+1)+b^2*(c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+1)+d^2*e*g*(m+n+2)))*x)/
                    (b*d*(b*c-a*d)^2*(m+1)*(n+1))*(a+b*x)^(m+1)*(c+d*x)^(n+1) -
                  (a^2*d^2*f*h*(2+3*n+n^2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
                      b^2*(c^2*f*h*(2+3*m+m^2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(6+m^2+5*n+n^2+m*(2*n+5))))/
                    (b*d*(b*c-a*d)^2*(m+1)*(n+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n+1),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && LtQ[m,-1] && LtQ[n,-1]",
                desc: "Apply a recurrence relation that reduces the integral.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, f__, g__, h__],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && ltq!(m_, -1)
                        && ltq!(n_, -1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let m1 = &m_ + Atom::num(1);
                    let n1 = &n_ + Atom::num(1);
                    let m_n_2 = &m_ + &n_ + Atom::num(2);
                    let m_n_3 = &m_ + &n_ + Atom::num(3);
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let denominator = &b__ * &d__ * bc_ad.pow(2) * &m1 * &n1;
                    let linear =
                        b__.pow(2) * &c__ * &d__ * &e__ * &g__ * &n1
                            + a__.pow(2) * &c__ * &d__ * &f__ * &h__ * &n1
                            + &a__
                                * &b__
                                * (d__.pow(2) * &e__ * &g__ * &m1
                                    + c__.pow(2) * &f__ * &h__ * &m1
                                    - &c__ * &d__ * &fg_eh * &m_n_2)
                            + (a__.pow(2) * d__.pow(2) * &f__ * &h__ * &n1
                                - &a__ * &b__ * d__.pow(2) * &fg_eh * &n1
                                + b__.pow(2)
                                    * (c__.pow(2) * &f__ * &h__ * &m1
                                        - &c__ * &d__ * &fg_eh * &m1
                                        + d__.pow(2) * &e__ * &g__ * &m_n_2))
                                * x_;
                    let recurrence_numerator =
                        a__.pow(2)
                            * d__.pow(2)
                            * &f__
                            * &h__
                            * (Atom::num(2) + Atom::num(3) * &n_ + n_.pow(2))
                            + &a__
                                * &b__
                                * &d__
                                * &n1
                                * (Atom::num(2) * &c__ * &f__ * &h__ * &m1
                                    - &d__ * &fg_eh * &m_n_3)
                            + b__.pow(2)
                                * (c__.pow(2)
                                    * &f__
                                    * &h__
                                    * (Atom::num(2)
                                        + Atom::num(3) * &m_
                                        + m_.pow(2))
                                    - &c__ * &d__ * &fg_eh * &m1 * &m_n_3
                                    + d__.pow(2)
                                        * &e__
                                        * &g__
                                        * (Atom::num(6)
                                            + m_.pow(2)
                                            + Atom::num(5) * &n_
                                            + n_.pow(2)
                                            + &m_ * (Atom::num(2) * &n_ + Atom::num(5))));
                    let recursive = rubi_rhs_int(&(first.pow(&m1) * second.pow(&n1)), x_);
                    rubi_simp(&(linear * first.pow(&m1) * second.pow(&n1)
                            / &denominator), x_)
                            - rubi_star(recurrence_numerator / denominator, recursive)
                },
            ));
}

fn push_rules_rule_162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 162,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
                  (b^3*c*e*g*(m+2)-a^3*d*f*h*(n+2)-a^2*b*(c*f*h*m-d*(f*g+e*h)*(m+n+3))-a*b^2*(c*(f*g+e*h)+d*e*g*(2*m+n+4))+
                      b*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2)))*x)/
                    (b^2*(b*c-a*d)^2*(m+1)*(m+2))*(a+b*x)^(m+1)*(c+d*x)^(n+1) +
                  (f*h/b^2-(d*(m+n+3)*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2))))/
                      (b^2*(b*c-a*d)^2*(m+1)*(m+2))) \\[Star]
                    Int[(a+b*x)^(m+2)*(c+d*x)^n,x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (LtQ[m,-2] || EqQ[m+n+3,0] && Not[LtQ[n,-2]])",
                desc: "Apply a recurrence relation that reduces the integral.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, f__, g__, h__, n_],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                        && (ltq!(m_, -2) || eqq!(&m_ + &n_ + Atom::num(3), Atom::num(0)) && !ltq!(n_, -2))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let m1 = &m_ + Atom::num(1);
                    let m2 = &m_ + Atom::num(2);
                    let n1 = &n_ + Atom::num(1);
                    let n2 = &n_ + Atom::num(2);
                    let m_n_2 = &m_ + &n_ + Atom::num(2);
                    let m_n_3 = &m_ + &n_ + Atom::num(3);
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let bracket = a__.pow(2) * &d__ * &f__ * &h__ * (&m_ - &n_)
                        - &a__
                            * &b__
                            * (Atom::num(2) * &c__ * &f__ * &h__ * &m1 - &d__ * &fg_eh * &n1)
                        + b__.pow(2)
                            * (&c__ * &fg_eh * &m1 - &d__ * &e__ * &g__ * &m_n_2);
                    let denominator = b__.pow(2) * bc_ad.pow(2) * &m1 * &m2;
                    let linear = b__.pow(3) * &c__ * &e__ * &g__ * &m2
                        - a__.pow(3) * &d__ * &f__ * &h__ * &n2
                        - a__.pow(2)
                            * &b__
                            * (&c__ * &f__ * &h__ * &m_ - &d__ * &fg_eh * &m_n_3)
                        - &a__
                            * b__.pow(2)
                            * (&c__ * &fg_eh + &d__ * &e__ * &g__ * (Atom::num(2) * &m_ + &n_ + Atom::num(4)))
                        + &b__ * &bracket * x_;
                    let recurrence_coefficient = &f__ * &h__ / b__.pow(2)
                        - &d__ * &m_n_3 * &bracket / &denominator;
                    let recursive = rubi_rhs_int(&(first.pow(m2) * second.pow(n_)), x_);
                    rubi_simp(&(linear * first.pow(&m1) * second.pow(&n1)
                            / denominator), x_)
                            + rubi_star(recurrence_coefficient, recursive)
                },
            ));
}

fn push_rules_rule_163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 163,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
                  (a^2*d*f*h*(n+2)+b^2*d*e*g*(m+n+3)+a*b*(c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+b*f*h*(b*c-a*d)*(m+1)*x)/
                    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3))*(a+b*x)^(m+1)*(c+d*x)^(n+1) -
                  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
                      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
                    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (GeQ[m,-2] && LtQ[m,-1] || SumSimplerQ[m,1]) && NeQ[m,-1] && NeQ[m+n+3,0]",
                desc: "Apply a recurrence relation that reduces the integral.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, f__, g__, h__, n_],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                        && ((geq!(m_, -2) && ltq!(m_, -1)) || sum_simplerq!(m_, 1))
                        && neq!(m_, -Atom::num(1))
                        && neq!(&m_ + &n_ + Atom::num(3), Atom::num(0))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let m1 = &m_ + Atom::num(1);
                    let m2 = &m_ + Atom::num(2);
                    let n1 = &n_ + Atom::num(1);
                    let n2 = &n_ + Atom::num(2);
                    let m_n_2 = &m_ + &n_ + Atom::num(2);
                    let m_n_3 = &m_ + &n_ + Atom::num(3);
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let denominator = b__.pow(2) * &d__ * &bc_ad * &m1 * &m_n_3;
                    let direct_numerator = a__.pow(2) * &d__ * &f__ * &h__ * &n2
                        + b__.pow(2) * &d__ * &e__ * &g__ * &m_n_3
                        + &a__ * &b__ * (&c__ * &f__ * &h__ * &m1 - &d__ * &fg_eh * &m_n_3)
                        + &b__ * &f__ * &h__ * &bc_ad * &m1 * x_;
                    let recurrence_numerator = a__.pow(2)
                        * d__.pow(2)
                        * &f__
                        * &h__
                        * &n1
                        * &n2
                        + &a__
                            * &b__
                            * &d__
                            * &n1
                            * (Atom::num(2) * &c__ * &f__ * &h__ * &m1 - &d__ * &fg_eh * &m_n_3)
                        + b__.pow(2)
                            * (c__.pow(2) * &f__ * &h__ * &m1 * &m2
                                - &c__ * &d__ * &fg_eh * &m1 * &m_n_3
                                + d__.pow(2) * &e__ * &g__ * &m_n_2 * &m_n_3);
                    let recursive = rubi_rhs_int(&(first.pow(&m1) * second.pow(n_)), x_);
                    rubi_simp(&(direct_numerator * first.pow(&m1) * second.pow(&n1)
                            / &denominator), x_)
                            - rubi_star(recurrence_numerator / denominator, recursive)
                },
            ));
}

fn push_rules_rule_164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 164,
                source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_] :=
                  -(a*d*f*h*(n+2)+b*c*f*h*(m+2)-b*d*(f*g+e*h)*(m+n+3)-b*d*f*h*(m+n+2)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
                    (b^2*d^2*(m+n+2)*(m+n+3)) +
                  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
                      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
                    (b^2*d^2*(m+n+2)*(m+n+3)) \\[Star] Int[(a+b*x)^m*(c+d*x)^n,x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && NeQ[m+n+2,0] && NeQ[m+n+3,0]",
                desc: "Apply a recurrence relation that reduces the integral.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, f__, g__, h__, m_, n_],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                        && neq!(&m_ + &n_ + Atom::num(2), Atom::num(0))
                        && neq!(&m_ + &n_ + Atom::num(3), Atom::num(0))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let m1 = &m_ + Atom::num(1);
                    let m2 = &m_ + Atom::num(2);
                    let n1 = &n_ + Atom::num(1);
                    let n2 = &n_ + Atom::num(2);
                    let m_n_2 = &m_ + &n_ + Atom::num(2);
                    let m_n_3 = &m_ + &n_ + Atom::num(3);
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let denominator =
                        b__.pow(2) * d__.pow(2) * &m_n_2 * &m_n_3;
                    let direct_numerator = &a__ * &d__ * &f__ * &h__ * &n2
                        + &b__ * &c__ * &f__ * &h__ * &m2
                        - &b__ * &d__ * &fg_eh * &m_n_3
                        - &b__ * &d__ * &f__ * &h__ * &m_n_2 * x_;
                    let recurrence_numerator = a__.pow(2)
                        * d__.pow(2)
                        * &f__
                        * &h__
                        * &n1
                        * &n2
                        + &a__
                            * &b__
                            * &d__
                            * &n1
                            * (Atom::num(2) * &c__ * &f__ * &h__ * &m1 - &d__ * &fg_eh * &m_n_3)
                        + b__.pow(2)
                            * (c__.pow(2) * &f__ * &h__ * &m1 * &m2
                                - &c__ * &d__ * &fg_eh * &m1 * &m_n_3
                                + d__.pow(2) * &e__ * &g__ * &m_n_2 * &m_n_3);
                    let recursive = rubi_rhs_int(&(first.pow(m_) * second.pow(n_)), x_);
                    rubi_simp(&(-direct_numerator * first.pow(&m1) * second.pow(&n1)
                            / &denominator), x_)
                            + rubi_star(recurrence_numerator / denominator, recursive)
                },
            ));
}

fn push_rules_rule_165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 165,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && (IntegersQ[m,n,p] || IGtQ[n,0] && IGtQ[p,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && (integersq!([m_, n_, p_])
                    || igtq!(n_, 0) && igtq!(p_, 0))
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_)
                * (c__ + d__ * x_).pow(n_)
                * (e__ + f__ * x_).pow(p_)
                * (g__ + h__ * x_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    );
    rules.push(
        rule.with_early_numeric_bound(n_, RubiEarlyNumericBound::Integer)
            .with_early_numeric_bound(p_, RubiEarlyNumericBound::Integer),
    );
}

fn push_rules_rule_166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 166,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) -
          1/(b*(b*e-a*f)*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
            Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p},x] && ILtQ[m,-1] && GtQ[n,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && iltq!(m_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ + Atom::num(1);
            let n1 = &n_ - Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let n_p_1 = &n_ + &p_ + Atom::num(1);
            let b_e_a_f = &b__ * &e__ - &a__ * &f__;
            let b_g_a_h = &b__ * &g__ - &a__ * &h__;
            let f_g_e_h = &f__ * &g__ - &e__ * &h__;
            let denominator = &b__ * &b_e_a_f * &m1;
            let simp = simp!(
                &b__ * &c__ * &f_g_e_h * &m1
                    + &b_g_a_h * (&d__ * &e__ * &n_ + &c__ * &f__ * &p1)
                    + &d__ * (&b__ * &f_g_e_h * &m1 + &f__ * &b_g_a_h * &n_p_1) * x_,
                x_
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(n1) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(&b_g_a_h * first.pow(&m1) * second.pow(&n_) * third.pow(&p1)
                    / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(
        rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::IntegerLessThan(-1))
            .with_early_numeric_bound(n_, RubiEarlyNumericBound::IntegerGreaterThan(0)),
    );
}

fn push_rules_rule_167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 167,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) -
          1/(b*(b*e-a*f)*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
            Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p},x] && LtQ[m,-1] && GtQ[n,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_,
                ])
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ + Atom::num(1);
            let n1 = &n_ - Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let n_p_1 = &n_ + &p_ + Atom::num(1);
            let b_e_a_f = &b__ * &e__ - &a__ * &f__;
            let b_g_a_h = &b__ * &g__ - &a__ * &h__;
            let f_g_e_h = &f__ * &g__ - &e__ * &h__;
            let denominator = &b__ * &b_e_a_f * &m1;
            let simp = simp!(
                &b__ * &c__ * &f_g_e_h * &m1
                    + &b_g_a_h * (&d__ * &e__ * &n_ + &c__ * &f__ * &p1)
                    + &d__ * (&b__ * &f_g_e_h * &m1 + &f__ * &b_g_a_h * &n_p_1) * x_,
                x_
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(n1) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(&b_g_a_h * first.pow(&m1) * second.pow(&n_) * third.pow(&p1)
                    / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(
        rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::NumberLessThan(-1))
            .with_early_numeric_bound(n_, RubiEarlyNumericBound::NumberGreaterThan(0)),
    );
}

fn push_rules_rule_168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 168,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                && iltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ + Atom::num(1);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let m_n_p_3 = &m_ + &n_ + &p_ + Atom::num(3);
            let b_c_a_d = &b__ * &c__ - &a__ * &d__;
            let b_e_a_f = &b__ * &e__ - &a__ * &f__;
            let b_g_a_h = &b__ * &g__ - &a__ * &h__;
            let denominator = &m1 * &b_c_a_d * &b_e_a_f;
            let simp = simp!(
                (&a__ * &d__ * &f__ * &g__ - &b__ * (&d__ * &e__ + &c__ * &f__) * &g__ + &b__ * &c__ * &e__ * &h__)
                    * &m1
                    - &b_g_a_h * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1)
                    - &d__ * &f__ * &b_g_a_h * &m_n_p_3 * x_,
                x_
            );
            let direct = &b_g_a_h
                    * first.pow(&m1)
                    * second.pow(&n1)
                    * third.pow(&p1)
                    / &denominator;
            let recursive = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(n_) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::IntegerLessThan(-1)));
}

fn push_rules_rule_169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 169,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                && ltq!(m_, -1)
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_,
                ])
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ + Atom::num(1);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let m_n_p_3 = &m_ + &n_ + &p_ + Atom::num(3);
            let b_c_a_d = &b__ * &c__ - &a__ * &d__;
            let b_e_a_f = &b__ * &e__ - &a__ * &f__;
            let b_g_a_h = &b__ * &g__ - &a__ * &h__;
            let denominator = &m1 * &b_c_a_d * &b_e_a_f;
            let simp = simp!(
                (&a__ * &d__ * &f__ * &g__ - &b__ * (&d__ * &e__ + &c__ * &f__) * &g__ + &b__ * &c__ * &e__ * &h__)
                    * &m1
                    - &b_g_a_h * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1)
                    - &d__ * &f__ * &b_g_a_h * &m_n_p_3 * x_,
                x_
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&m1) * second.pow(n_) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(&b_g_a_h
                    * first.pow(&m1)
                    * second.pow(&n1)
                    * third.pow(&p1)
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::NumberLessThan(-1)));
}

fn push_rules_rule_170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 170,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) +
          1/(d*f*(m+n+p+2)) \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
            Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && GtQ[m,0] && NeQ[m+n+p+2,0] && IntegerQ[m]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                && gtq!(m_, 0)
                && neq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
                && integerq!(m_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ - Atom::num(1);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let m_n_1 = &m_ + &n_ + Atom::num(1);
            let m_p_1 = &m_ + &p_ + Atom::num(1);
            let m_n_p_2 = &m_ + &n_ + &p_ + Atom::num(2);
            let denominator = &d__ * &f__ * &m_n_p_2;
            let simp = simp!(
                &a__ * &d__ * &f__ * &g__ * &m_n_p_2
                    - &h__ * (&b__ * &c__ * &e__ * &m_ + &a__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    + (&b__ * &d__ * &f__ * &g__ * &m_n_p_2
                        + &h__ * (&a__ * &d__ * &f__ * &m_
                            - &b__ * (&d__ * &e__ * &m_n_1 + &c__ * &f__ * &m_p_1)))
                        * x_,
                x_
            );
            let recursive = rubi_rhs_int(
                &(first.pow(m1) * second.pow(n_) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(&h__ * first.pow(&m_) * second.pow(&n1) * third.pow(&p1)
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::IntegerGreaterThan(0)));
}

fn push_rules_rule_171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    let rule = rubi_rule!(
        order: 171,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
          h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) +
          1/(d*f*(m+n+p+2)) \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
            Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && GtQ[m,0] && NeQ[m+n+p+2,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                && gtq!(m_, 0)
                && neq!(&m_ + &n_ + &p_ + Atom::num(2), Atom::num(0))
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_,
                ])
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let m1 = &m_ - Atom::num(1);
            let n1 = &n_ + Atom::num(1);
            let p1 = &p_ + Atom::num(1);
            let m_n_1 = &m_ + &n_ + Atom::num(1);
            let m_p_1 = &m_ + &p_ + Atom::num(1);
            let m_n_p_2 = &m_ + &n_ + &p_ + Atom::num(2);
            let denominator = &d__ * &f__ * &m_n_p_2;
            let simp = simp!(
                &a__ * &d__ * &f__ * &g__ * &m_n_p_2
                    - &h__ * (&b__ * &c__ * &e__ * &m_ + &a__ * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1))
                    + (&b__ * &d__ * &f__ * &g__ * &m_n_p_2
                        + &h__ * (&a__ * &d__ * &f__ * &m_
                            - &b__ * (&d__ * &e__ * &m_n_1 + &c__ * &f__ * &m_p_1)))
                        * x_,
                x_
            );
            let recursive = rubi_rhs_int(
                &(first.pow(m1) * second.pow(n_) * third.pow(p_) * simp),
                x_,
            );
            rubi_simp(&(&h__ * first.pow(&m_) * second.pow(&n1) * third.pow(&p1)
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(rule.with_early_numeric_bound(m_, RubiEarlyNumericBound::NumberGreaterThan(0)));
}

fn push_rules_rule_172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 172,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
                  With[{mnp=Simplify[m+n+p]},
                  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
                  1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
                    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(mnp+3)*x,x],x] /;
                 ILtQ[mnp+2,0] && (SumSimplerQ[m,1] || Not[NeQ[n,-1] && SumSimplerQ[n,1]] && Not[NeQ[p,-1] && SumSimplerQ[p,1]])] /;
                FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && NeQ[m,-1]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_1(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                x_free: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_],
                when: {
                    let mnp = rubi_simplify(&(&m_ + &n_ + &p_));
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                        && iltq!(&mnp + Atom::num(2), 0)
                        && neq!(m_, -Atom::num(1))
                        && (sum_simplerq!(m_, 1)
                            || !(neq!(n_, -Atom::num(1)) && sum_simplerq!(n_, 1))
                                && !(neq!(p_, -Atom::num(1)) && sum_simplerq!(p_, 1)))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let m1 = &m_ + Atom::num(1);
                    let n1 = &n_ + Atom::num(1);
                    let p1 = &p_ + Atom::num(1);
                    let mnp = rubi_simplify(&(&m_ + &n_ + &p_));
                    let m_n_p_3 = mnp + Atom::num(3);
                    let b_c_a_d = &b__ * &c__ - &a__ * &d__;
                    let b_e_a_f = &b__ * &e__ - &a__ * &f__;
                    let b_g_a_h = &b__ * &g__ - &a__ * &h__;
                    let denominator = &m1 * &b_c_a_d * &b_e_a_f;
                    let simp = simp!(
                        (&a__ * &d__ * &f__ * &g__ - &b__ * (&d__ * &e__ + &c__ * &f__) * &g__ + &b__ * &c__ * &e__ * &h__)
                            * &m1
                            - &b_g_a_h * (&d__ * &e__ * &n1 + &c__ * &f__ * &p1)
                            - &d__ * &f__ * &b_g_a_h * &m_n_p_3 * x_,
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m1) * second.pow(n_) * third.pow(p_) * simp),
                        x_,
                    );
                    rubi_simp(&(&b_g_a_h
                            * first.pow(&m1)
                            * second.pow(&n1)
                            * third.pow(&p1)
                            / &denominator), x_)
                            + rubi_star(Atom::num(1) / denominator, recursive)
                },
            ));
}

fn push_rules_rule_173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 173,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(g_.+h_.*x_)/(e_.+f_.*x_),x_] :=
                  (f*g-e*h)*(c*f-d*e)^(m+n+1)/f^(m+n+2) \\[Star] Int[(a+b*x)^m/((c+d*x)^(m+1)*(e+f*x)),x] +
                  1/f^(m+n+2) \\[Star] Int[(a+b*x)^m/(c+d*x)^(m+1)*
                    ExpandToSum[(f^(m+n+2)*(c+d*x)^(m+n+1)*(g+h*x)-(f*g-e*h)*(c*f-d*e)^(m+n+1))/(e+f*x),x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[m+n+1,0] && (LtQ[m,0] || SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])",
                desc: "Expand the integrand and integrate the resulting terms.",
                refs: [],
                pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (g__ + h__ * x_) / (e__ + f__ * x_),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && igtq!(&m_ + &n_ + Atom::num(1), 0)
                        && (ltq!(m_, 0) || sum_simplerq!(m_, 1) || !sum_simplerq!(n_, 1))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let denominator_affine = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let cross = &f__ * &g__ - &e__ * &h__;
                    let delta = &c__ * &f__ - &d__ * &e__;
                    let mn1 = &m_ + &n_ + Atom::num(1);
                    let f_power = f__.pow(&mn1 + Atom::num(1));
                    let expand_argument = (&f_power * second.pow(&mn1) * fourth
                        - &cross * delta.pow(&mn1))
                        / &denominator_affine;
                    let expanded_to_sum = rubi_expand_to_sum(&expand_argument, x_);
                    let first_recursive = rubi_rhs_int(
                        &(first.pow(&m_)
                            / (second.pow(&m_ + Atom::num(1))
                                * &denominator_affine)),
                        x_,
                    );
                    let second_recursive = rubi_rhs_int(
                        &(first.pow(&m_)
                            / second.pow(&m_ + Atom::num(1))
                            * expanded_to_sum),
                        x_,
                    );
                    rubi_star(&cross * delta.pow(mn1) / &f_power, first_recursive) + rubi_star(Atom::num(1) / f_power, second_recursive)
                },
            ));
}

fn push_rules_rule_174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 174,
        source: "Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          (b*g-a*h)/(b*c-a*d) \\[Star] Int[(e+f*x)^p/(a+b*x),x] -
          (d*g-c*h)/(b*c-a*d) \\[Star] Int[(e+f*x)^p/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(p_) * (g__ + h__ * x_) / ((a__ + b__ * x_) * (c__ + d__ * x_)),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_recursive = rubi_rhs_int(&(third.pow(&p_) / first), x_);
            let second_recursive = rubi_rhs_int(&(third.pow(p_) / second), x_);
            rubi_star((&b__ * &g__ - &a__ * &h__) / &determinant, first_recursive) - rubi_star((&d__ * &g__ - &c__ * &h__) / determinant, second_recursive)
        },
    ));
}

fn push_rules_rule_175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 175,
                source: "Int[(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)/(a_.+b_.*x_),x_] :=
                  h/b \\[Star] Int[(c+d*x)^n*(e+f*x)^p,x] + (b*g-a*h)/b \\[Star] Int[(c+d*x)^n*(e+f*x)^p/(a+b*x),x] /;
                FreeQ[{a,b,c,d,e,f,g,h,n,p},x]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern: (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_) * (g__ + h__ * x_) / (a__ + b__ * x_),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_, p_], x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let first_recursive =
                        rubi_rhs_int(&(second.pow(&n_) * third.pow(&p_)), x_);
                    let second_recursive =
                        rubi_rhs_int(&(second.pow(n_) * third.pow(p_) / first), x_);
                    rubi_star(&h__ / &b__, first_recursive)
                            + rubi_star((&b__ * &g__ - &a__ * &h__) / &b__, second_recursive)
                },
            ));
}

fn push_rules_rule_176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 176,
                source: "Int[(g_.+h_.*x_)/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_] :=
                  h/f \\[Star] Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]),x] + (f*g-e*h)/f \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && SimplerQ[a+b*x,e+f*x] && SimplerQ[c+d*x,e+f*x]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern: (g__ + h__ * x_) / ((a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, g__, h__, d__, f__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && simplerq!(&a__ + &b__ * x_, &e__ + &f__ * x_)
                        && simplerq!(&c__ + &d__ * x_, &e__ + &f__ * x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let first_recursive = rubi_rhs_int(
                        &(&third.sqrt()
                            / (&first.sqrt() * &second.sqrt())),
                        x_,
                    );
                    let second_recursive = rubi_rhs_int(
                        &(Atom::num(1) / (first.sqrt() * second.sqrt() * third.sqrt())),
                        x_,
                    );
                    rubi_star(&h__ / &f__, first_recursive)
                            + rubi_star((&f__ * &g__ - &e__ * &h__) / &f__, second_recursive)
                },
            ));
}

fn push_rules_rule_177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 177,
                source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_] :=
                  h/b \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] + (b*g-a*h)/b \\[Star] Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern:  rubi_shared_pattern_1(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_)
                        && (sum_simplerq!(m_, 1)
                            || !sum_simplerq!(n_, 1) && !sum_simplerq!(p_, 1))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let product = second.pow(n_) * third.pow(p_);
                    let first_recursive =
                        rubi_rhs_int(&(first.pow(&m_ + Atom::num(1)) * &product), x_);
                    let second_recursive = rubi_rhs_int(&(first.pow(m_) * product), x_);
                    rubi_star(&h__ / &b__, first_recursive)
                            + rubi_star((&b__ * &g__ - &a__ * &h__) / &b__, second_recursive)
                },
            ));
}

fn push_rules_rule_178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 178,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_],x_] :=
                  (a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*(m+1)) -
                  1/(2*b*(m+1)) \\[Star] Int[(a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
                    Simp[d*e*g+c*f*g+c*e*h+2*(d*f*g+d*e*h+c*f*h)*x+3*d*f*h*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LtQ[m,-1]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_3(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && ltq!(m_, -1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let m1 = &m_ + Atom::num(1);
                    let radical_product = &second.sqrt() * &third.sqrt() * &fourth.sqrt();
                    let simp = simp!(
                        &d__ * &e__ * &g__
                            + &c__ * &f__ * &g__
                            + &c__ * &e__ * &h__
                            + Atom::num(2) * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__) * x_
                            + Atom::num(3) * &d__ * &f__ * &h__ * x_.pow(2),
                        x_
                    );
                    let recursive =
                        rubi_rhs_int(&(first.pow(&m1) / &radical_product * simp), x_);
                    rubi_simp(&(first.pow(&m1) * &radical_product / (&b__ * &m1)), x_)
                            - rubi_star(Atom::num(1)
                                    / (Atom::num(2) * &b__ * (&m_ + Atom::num(1))), recursive)
                },
            ));
}

fn push_rules_rule_179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 179,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_],x_] :=
                  2*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*(2*m+5)) +
                  1/(b*(2*m+5)) \\[Star] Int[((a+b*x)^m)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
                    Simp[3*b*c*e*g-a*(d*e*g+c*f*g+c*e*h)+2*(b*(d*e*g+c*f*g+c*e*h)-a*(d*f*g+d*e*h+c*f*h))*x-(3*a*d*f*h-b*(d*f*g+d*e*h+c*f*h))*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && Not[LtQ[m,-1]]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_3(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && !ltq!(m_, -1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let two_m_5 = Atom::num(2) * &m_ + Atom::num(5);
                    let radical_product = &second.sqrt() * &third.sqrt() * &fourth.sqrt();
                    let simp = simp!(
                        Atom::num(3) * &b__ * &c__ * &e__ * &g__
                            - &a__ * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                            + Atom::num(2)
                                * (&b__ * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                                    - &a__ * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__))
                                * x_
                            - (Atom::num(3) * &a__ * &d__ * &f__ * &h__
                                - &b__ * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__))
                                * x_.pow(2),
                        x_
                    );
                    let recursive =
                        rubi_rhs_int(&(first.pow(&m_) / &radical_product * simp), x_);
                    rubi_simp(&(Atom::num(2) * first.pow(&m_ + Atom::num(1)) * &radical_product
                            / (&b__ * &two_m_5)), x_)
                            + rubi_star(Atom::num(1) / (&b__ * two_m_5), recursive)
                },
            ));
}

fn push_rules_rule_180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 180,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/Sqrt[c_.+d_.*x_],x_] :=
                  2*(a+b*x)^m*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*(2*m+3)) -
                  1/(d*(2*m+3)) \\[Star] Int[((a+b*x)^(m-1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[2*b*c*e*g*m+a*(c*(f*g+e*h)-2*d*e*g*(m+1)) -
                      (b*(2*d*e*g-c*(f*g+e*h)*(2*m+1))-a*(2*c*f*h-d*(2*m+1)*(f*g+e*h)))*x -
                      (2*a*d*f*h*m+b*(d*(f*g+e*h)-2*c*f*h*(m+1)))*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && GtQ[m,0]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_5(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && gtq!(m_, 0)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let denominator_affine = &c__ + &d__ * x_;
                    let second = &e__ + &f__ * x_;
                    let third = &g__ + &h__ * x_;
                    let two_m_3 = Atom::num(2) * &m_ + Atom::num(3);
                    let radical_product =
                        &denominator_affine.sqrt() * &second.sqrt() * &third.sqrt();
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let simp = simp!(
                        Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m_
                            + &a__ * (&c__ * &fg_eh - Atom::num(2) * &d__ * &e__ * &g__ * (&m_ + Atom::num(1)))
                            - (&b__ * (Atom::num(2) * &d__ * &e__ * &g__ - &c__ * &fg_eh * (Atom::num(2) * &m_ + Atom::num(1)))
                                - &a__ * (Atom::num(2) * &c__ * &f__ * &h__ - &d__ * (Atom::num(2) * &m_ + Atom::num(1)) * &fg_eh))
                                * x_
                            - (Atom::num(2) * &a__ * &d__ * &f__ * &h__ * &m_
                                + &b__ * (&d__ * &fg_eh - Atom::num(2) * &c__ * &f__ * &h__ * (&m_ + Atom::num(1))))
                                * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_ - Atom::num(1)) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(Atom::num(2) * first.pow(&m_) * &radical_product
                            / (&d__ * &two_m_3)), x_)
                            - rubi_star(Atom::num(1) / (&d__ * two_m_3), recursive)
                },
            ));
}

fn push_rules_rule_181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 181,
                source: "Int[Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]),x_] :=
                  (b*e-a*f)*(b*g-a*h)/b^2 \\[Star] Int[1/((a+b*x)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
                  1/b^2 \\[Star] Int[Simp[b*f*g+b*e*h-a*f*h+b*f*h*x,x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern: (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt()
                    / ((a__ + b__ * x_) * (c__ + d__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let radical_denominator =
                        &second.sqrt() * &third.sqrt() * &fourth.sqrt();
                    let simp = simp!(&b__ * &f__ * &g__ + &b__ * &e__ * &h__ - &a__ * &f__ * &h__ + &b__ * &f__ * &h__ * x_, x_);
                    let first_recursive = rubi_rhs_int(
                        &(Atom::num(1) / (first * &radical_denominator)),
                        x_,
                    );
                    let second_recursive = rubi_rhs_int(&(simp / radical_denominator), x_);
                    rubi_star((&b__ * &e__ - &a__ * &f__)
                                * (&b__ * &g__ - &a__ * &h__)
                                / b__.pow(2), first_recursive) + rubi_star(Atom::num(1) / b__.pow(2), second_recursive)
                },
            ));
}

fn push_rules_rule_182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 182,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/Sqrt[c_.+d_.*x_],x_] :=
                  (a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)) -
                  1/(2*(m+1)*(b*c-a*d)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[c*(f*g+e*h)+d*e*g*(2*m+3)+2*(c*f*h+d*(m+2)*(f*g+e*h))*x+d*f*h*(2*m+5)*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LtQ[m,-1]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_5(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && ltq!(m_, -1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let denominator_affine = &c__ + &d__ * x_;
                    let second = &e__ + &f__ * x_;
                    let third = &g__ + &h__ * x_;
                    let m_plus_1 = &m_ + Atom::num(1);
                    let determinant = &b__ * &c__ - &a__ * &d__;
                    let radical_product =
                        denominator_affine.sqrt() * second.sqrt() * third.sqrt();
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let denominator = &m_plus_1 * &determinant;
                    let simp = simp!(
                        &c__ * &fg_eh
                            + &d__ * &e__ * &g__ * (Atom::num(2) * &m_ + Atom::num(3))
                            + Atom::num(2)
                                * (&c__ * &f__ * &h__ + &d__ * (&m_ + Atom::num(2)) * &fg_eh)
                                * x_
                            + &d__
                                * &f__
                                * &h__
                                * (Atom::num(2) * &m_ + Atom::num(5))
                                * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_plus_1) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(first.pow(&m_plus_1) * &radical_product / &denominator), x_)
                            - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
                },
            ));
}

fn push_rules_rule_183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 183,
                source: "Int[Sqrt[a_.+b_.*x_]/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  2*(a+b*x)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/(Sqrt[c+d*x]*Sqrt[e+f*x]) \\[Star]
                    Subst[Int[1/((h-b*x^2)*Sqrt[1+(b*c-a*d)*x^2/(d*g-c*h)]*Sqrt[1+(b*e-a*f)*x^2/(f*g-e*h)]),x],x,Sqrt[g+h*x]/Sqrt[a+b*x]] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Substitute a new variable and integrate the transformed expression.",
                refs: [],
                pattern: (a__ + b__ * x_).sqrt()
                    / ((c__ + d__ * x_).sqrt()
                        * (e__ + f__ * x_).sqrt()
                        * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let sub_guard = fresh_substitution_symbol().unwrap();
                    let sub_symbol = sub_guard.symbol();
                    let sub = Atom::var(sub_symbol);
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let bg_ah = &b__ * &g__ - &a__ * &h__;
                    let dg_ch = &d__ * &g__ - &c__ * &h__;
                    let fg_eh = &f__ * &g__ - &e__ * &h__;
                    let transformed_integrand = Atom::num(1)
                        / ((&h__ - &b__ * sub.pow(2))
                            * (Atom::num(1)
                                + (&b__ * &c__ - &a__ * &d__) * sub.pow(2) / &dg_ch)
                                .sqrt()
                            * (Atom::num(1)
                                + (&b__ * &e__ - &a__ * &f__) * sub.pow(2) / &fg_eh)
                                .sqrt());
                    let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
                    let substitution = fourth.sqrt() / &first.sqrt();
                    let multiplier = Atom::num(2)
                        * &first
                        * (&bg_ah * &second / (&dg_ch * &first)).sqrt()
                        * (bg_ah * &third / (fg_eh * &first)).sqrt()
                        / (second.sqrt() * third.sqrt());
                    let substituted = substitute_symbol(&transformed, sub_symbol, substitution);
                    rubi_star(multiplier, substituted)
                },
            ));
}

fn push_rules_rule_184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 184,
        source: "Int[(a_.+b_.*x_)^(3/2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  b/d \\[Star] Int[Sqrt[a+b*x]*Sqrt[c+d*x]/(Sqrt[e+f*x]*Sqrt[g+h*x]),x] -
                  (b*c-a*d)/d \\[Star] Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * x_).pow((3, 2))
            / ((c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let radical_denominator = third.sqrt() * fourth.sqrt();
            let first_integrand =
                &first.sqrt() * &second.sqrt() / &radical_denominator;
            let second_integrand =
                first.sqrt() / (second.sqrt() * radical_denominator);
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);
            rubi_star(&b__ / &d__, first_recursive)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / d__, second_recursive)
        },
    ));
}

fn push_rules_rule_185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 185,
                source: "Int[(a_.+b_.*x_)^m_/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  2*b^2*(a+b*x)^(m-2)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m-1)) -
                  1/(d*f*h*(2*m-1)) \\[Star] Int[((a+b*x)^(m-3)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[a*b^2*(d*e*g+c*f*g+c*e*h)+2*b^3*c*e*g*(m-2)-a^3*d*f*h*(2*m-1) +
                      b*(2*a*b*(d*f*g+d*e*h+c*f*h)+b^2*(2*m-3)*(d*e*g+c*f*g+c*e*h)-3*a^2*d*f*h*(2*m-1))*x -
                      2*b^2*(m-1)*(3*a*d*f*h-b*(d*f*g+d*e*h+c*f*h))*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[2*m] && GeQ[m,2]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_6(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && geq!(m_, 2)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
                    let two_m_minus_1 = Atom::num(2) * &m_ - Atom::num(1);
                    let first_sum = &d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__;
                    let second_sum = &d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__;
                    let b2 = b__.pow(2);
                    let b3 = b__.pow(3);
                    let a2 = a__.pow(2);
                    let a3 = a__.pow(3);
                    let denominator = &d__ * &f__ * &h__ * &two_m_minus_1;
                    let simp = simp!(
                        &a__ * &b2 * &first_sum
                            + Atom::num(2) * &b3 * &c__ * &e__ * &g__ * (&m_ - Atom::num(2))
                            - &a3 * &d__ * &f__ * &h__ * &two_m_minus_1
                            + &b__
                                * (Atom::num(2) * &a__ * &b__ * &second_sum
                                    + &b2 * (Atom::num(2) * &m_ - Atom::num(3)) * &first_sum
                                    - Atom::num(3) * &a2 * &d__ * &f__ * &h__ * &two_m_minus_1)
                                * x_
                            - Atom::num(2)
                                * &b2
                                * (&m_ - Atom::num(1))
                                * (Atom::num(3) * &a__ * &d__ * &f__ * &h__ - &b__ * &second_sum)
                                * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_ - Atom::num(3)) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(Atom::num(2)
                            * b2
                            * first.pow(&m_ - Atom::num(2))
                            * &radical_product
                            / &denominator), x_)
                            - rubi_star(Atom::num(1) / denominator, recursive)
                },
            ));
}

fn push_rules_rule_186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 186,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
          -2 \\[Star] Subst[Int[1/(Simp[b*c-a*d-b*x^2,x]*Sqrt[Simp[(d*e-c*f)/d+f*x^2/d,x]]*Sqrt[Simp[(d*g-c*h)/d+h*x^2/d,x]]),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && GtQ[(d*e-c*f)/d,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && gtq!((&d__ * &e__ - &c__ * &f__) / &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / (simp!(&b__ * &c__ - &a__ * &d__ - &b__ * sub.pow(2), sub_symbol)
                    * simp!(
                        (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * sub.pow(2) / &d__,
                        sub_symbol
                    )
                    .sqrt()
                    * simp!(
                        (&d__ * &g__ - &c__ * &h__) / &d__ + &h__ * sub.pow(2) / &d__,
                        sub_symbol
                    )
                    .sqrt());
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted =
                substitute_symbol(&transformed, sub_symbol, (&c__ + &d__ * x_).sqrt());
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 187,
        source: "Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
          -2 \\[Star] Subst[Int[1/(Simp[b*c-a*d-b*x^2,x]*Sqrt[Simp[(d*e-c*f)/d+f*x^2/d,x]]*Sqrt[Simp[(d*g-c*h)/d+h*x^2/d,x]]),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && Not[SimplerQ[e+f*x,c+d*x]] && Not[SimplerQ[g+h*x,c+d*x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && !simplerq!(
                    &e__ + &f__ * x_,
                    &c__ + &d__ * x_
                )
                && !simplerq!(
                    &g__ + &h__ * x_,
                    &c__ + &d__ * x_
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / (simp!(&b__ * &c__ - &a__ * &d__ - &b__ * sub.pow(2), sub_symbol)
                    * simp!(
                        (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * sub.pow(2) / &d__,
                        sub_symbol
                    )
                    .sqrt()
                    * simp!(
                        (&d__ * &g__ - &c__ * &h__) / &d__ + &h__ * sub.pow(2) / &d__,
                        sub_symbol
                    )
                    .sqrt());
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted =
                substitute_symbol(&transformed, sub_symbol, (&c__ + &d__ * x_).sqrt());
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 188,
                source: "Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  2*Sqrt[g+h*x]*Sqrt[(b*e-a*f)*(c+d*x)/((d*e-c*f)*(a+b*x))]/
                    ((f*g-e*h)*Sqrt[c+d*x]*Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))]) \\[Star]
                    Subst[Int[1/(Sqrt[1+(b*c-a*d)*x^2/(d*e-c*f)]*Sqrt[1-(b*g-a*h)*x^2/(f*g-e*h)]),x],x,Sqrt[e+f*x]/Sqrt[a+b*x]] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Substitute a new variable and integrate the transformed expression.",
                refs: [],
                pattern: Atom::num(1)
                    / ((a__ + b__ * x_).sqrt()
                        * (c__ + d__ * x_).sqrt()
                        * (e__ + f__ * x_).sqrt()
                        * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let sub_guard = fresh_substitution_symbol().unwrap();
                    let sub_symbol = sub_guard.symbol();
                    let sub = Atom::var(sub_symbol);
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let be_af = &b__ * &e__ - &a__ * &f__;
                    let bg_ah = &b__ * &g__ - &a__ * &h__;
                    let de_cf = &d__ * &e__ - &c__ * &f__;
                    let fg_eh = &f__ * &g__ - &e__ * &h__;
                    let transformed_integrand = Atom::num(1)
                        / ((Atom::num(1) + &bc_ad * sub.pow(2) / &de_cf).sqrt()
                            * (Atom::num(1) - &bg_ah * sub.pow(2) / &fg_eh).sqrt());
                    let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
                    let substitution = third.sqrt() / &first.sqrt();
                    let multiplier = Atom::num(2)
                        * &fourth.sqrt()
                        * (&be_af * &second / (&de_cf * &first)).sqrt()
                        / (&fg_eh
                            * second.sqrt()
                            * (-(be_af * fourth) / (fg_eh * first)).sqrt());
                    let substituted = substitute_symbol(&transformed, sub_symbol, substitution);
                    rubi_star(multiplier, substituted)
                },
            ));
}

fn push_rules_rule_189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 189,
                source: "Int[1/((a_.+b_.*x_)^(3/2)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  -d/(b*c-a*d) \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
                  b/(b*c-a*d) \\[Star] Int[Sqrt[c+d*x]/((a+b*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern: Atom::num(1)
                    / ((a__ + b__ * x_).pow((3, 2))
                        * (c__ + d__ * x_).sqrt()
                        * (e__ + f__ * x_).sqrt()
                        * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let determinant = &b__ * &c__ - &a__ * &d__;
                    let first_integrand = Atom::num(1)
                        / (&first.sqrt()
                            * &second.sqrt()
                            * &third.sqrt()
                            * &fourth.sqrt());
                    let second_integrand = second.sqrt()
                        / (first.pow((3, 2)) * third.sqrt() * fourth.sqrt());
                    let first_recursive = rubi_rhs_int(&first_integrand, x_);
                    let second_recursive = rubi_rhs_int(&second_integrand, x_);
                    rubi_star(-&d__ / &determinant, first_recursive)
                            + rubi_star(&b__ / determinant, second_recursive)
                },
            ));
}

fn push_rules_rule_190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 190,
                source: "Int[(a_.+b_.*x_)^m_/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  b^2*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) -
                  1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h) -
                      2*b*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))*x + d*f*h*(2*m+5)*b^2*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[2*m] && LeQ[m,-2]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_6(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && leq!(m_, -2)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
                    let m_plus_1 = &m_ + Atom::num(1);
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let be_af = &b__ * &e__ - &a__ * &f__;
                    let bg_ah = &b__ * &g__ - &a__ * &h__;
                    let denominator = &m_plus_1 * &bc_ad * &be_af * &bg_ah;
                    let first_sum = &d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__;
                    let second_sum = &d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__;
                    let a2 = a__.pow(2);
                    let b2 = b__.pow(2);
                    let simp = simp!(
                        Atom::num(2) * &a2 * &d__ * &f__ * &h__ * &m_plus_1
                            - Atom::num(2) * &a__ * &b__ * &m_plus_1 * &second_sum
                            + &b2 * (Atom::num(2) * &m_ + Atom::num(3)) * &first_sum
                            - Atom::num(2)
                                * &b__
                                * (&a__ * &d__ * &f__ * &h__ * &m_plus_1
                                    - &b__ * (&m_ + Atom::num(2)) * &second_sum)
                                * x_
                            + &d__
                                * &f__
                                * &h__
                                * (Atom::num(2) * &m_ + Atom::num(5))
                                * &b2
                                * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_plus_1) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(b2 * first.pow(&m_plus_1) * &radical_product
                            / &denominator), x_)
                            - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
                },
            ));
}

fn push_rules_rule_191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 191,
                source: "Int[Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[g+h*x]/(h*Sqrt[e+f*x]) +
                  (d*e-c*f)*(b*f*g+b*e*h-2*a*f*h)/(2*f^2*h) \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
                  (a*d*f*h-b*(d*f*g+d*e*h-c*f*h))/(2*f^2*h) \\[Star] Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[g+h*x]),x] -
                  (d*e-c*f)*(f*g-e*h)/(2*f*h) \\[Star] Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*(e+f*x)^(3/2)*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern: (a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt()
                    / ((e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let f2 = f__.pow(2);
                    let de_cf = &d__ * &e__ - &c__ * &f__;
                    let fg_eh = &f__ * &g__ - &e__ * &h__;
                    let reciprocal_four_roots = Atom::num(1)
                        / (&first.sqrt()
                            * &second.sqrt()
                            * &third.sqrt()
                            * &fourth.sqrt());
                    let first_remainder_integrand = &third.sqrt()
                        / (&first.sqrt() * &second.sqrt() * &fourth.sqrt());
                    let second_remainder_integrand = &first.sqrt()
                        / (&second.sqrt()
                            * third.pow(Atom::num(3) / Atom::num(2))
                            * &fourth.sqrt());
                    let first_recursive = rubi_rhs_int(&reciprocal_four_roots, x_);
                    let second_recursive = rubi_rhs_int(&first_remainder_integrand, x_);
                    let third_recursive = rubi_rhs_int(&second_remainder_integrand, x_);
                    rubi_simp(&(first.sqrt() * second.sqrt() * fourth.sqrt() / (&h__ * third.sqrt())), x_)
                            + rubi_star(&de_cf
                                    * (&b__ * &f__ * &g__
                                        + &b__ * &e__ * &h__
                                        - Atom::num(2) * &a__ * &f__ * &h__)
                                    / (Atom::num(2) * &f2 * &h__), first_recursive)
                            + rubi_star((&a__ * &d__ * &f__ * &h__
                                    - &b__
                                        * (&d__ * &f__ * &g__
                                            + &d__ * &e__ * &h__
                                            - &c__ * &f__ * &h__))
                                    / (Atom::num(2) * f2 * &h__), second_recursive)
                            - rubi_star(de_cf * fg_eh / (Atom::num(2) * &f__ * &h__), third_recursive)
                },
            ));
}

fn push_rules_rule_192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 192,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  2*b*(a+b*x)^(m-1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(f*h*(2*m+1)) -
                  1/(f*h*(2*m+1)) \\[Star] Int[((a+b*x)^(m-2)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[a*b*(d*e*g+c*(f*g+e*h))+2*b^2*c*e*g*(m-1)-a^2*c*f*h*(2*m+1) +
                    (b^2*(2*m-1)*(d*e*g+c*(f*g+e*h))-a^2*d*f*h*(2*m+1)+2*a*b*(d*f*g+d*e*h-2*c*f*h*m))*x -
                    b*(a*d*f*h*(4*m-1)+b*(c*f*h-2*d*(f*g+e*h)*m))*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && GtQ[m,1]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_4(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && gtq!(m_, 1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
                    let two_m_plus_1 = Atom::num(2) * &m_ + Atom::num(1);
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let first_sum = &d__ * &e__ * &g__ + &c__ * &fg_eh;
                    let a2 = a__.pow(2);
                    let b2 = b__.pow(2);
                    let denominator = &f__ * &h__ * &two_m_plus_1;
                    let simp = simp!(
                        &a__ * &b__ * &first_sum
                            + Atom::num(2) * &b2 * &c__ * &e__ * &g__ * (&m_ - Atom::num(1))
                            - &a2 * &c__ * &f__ * &h__ * &two_m_plus_1
                            + (&b2 * (Atom::num(2) * &m_ - Atom::num(1)) * &first_sum
                                - &a2 * &d__ * &f__ * &h__ * &two_m_plus_1
                                + Atom::num(2)
                                    * &a__
                                    * &b__
                                    * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__
                                        - Atom::num(2) * &c__ * &f__ * &h__ * &m_))
                                * x_
                            - &b__
                                * (&a__ * &d__ * &f__ * &h__ * (Atom::num(4) * &m_ - Atom::num(1))
                                    + &b__
                                        * (&c__ * &f__ * &h__
                                            - Atom::num(2) * &d__ * &fg_eh * &m_))
                                * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_ - Atom::num(2)) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(Atom::num(2)
                            * &b__
                            * first.pow(&m_ - Atom::num(1))
                            * &radical_product
                            / &denominator), x_)
                            - rubi_star(Atom::num(1) / denominator, recursive)
                },
            ));
}

fn push_rules_rule_193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 193,
        source: "Int[Sqrt[c_.+d_.*x_]/((a_.+b_.*x_)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
          d/b \\[Star] Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
          (b*c-a*d)/b \\[Star] Int[1/((a+b*x)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_).sqrt()
            / ((a__ + b__ * x_)
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let first_integrand = Atom::num(1) / &radical_product;
            let second_integrand = Atom::num(1) / (first * radical_product);
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);
            rubi_star(&d__ / &b__, first_recursive)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / b__, second_recursive)
        },
    ));
}

fn push_rules_rule_194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 194,
                source: "Int[Sqrt[c_.+d_.*x_]/((a_.+b_.*x_)^(3/2)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  -2*Sqrt[c+d*x]*Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))]/
                    ((b*e-a*f)*Sqrt[g+h*x]*Sqrt[(b*e-a*f)*(c+d*x)/((d*e-c*f)*(a+b*x))]) \\[Star]
                    Subst[Int[Sqrt[1+(b*c-a*d)*x^2/(d*e-c*f)]/Sqrt[1-(b*g-a*h)*x^2/(f*g-e*h)],x],x,Sqrt[e+f*x]/Sqrt[a+b*x]] /;
                FreeQ[{a,b,c,d,e,f,g,h},x]",
                desc: "Substitute a new variable and integrate the transformed expression.",
                refs: [],
                pattern: (c__ + d__ * x_).sqrt()
                    / ((a__ + b__ * x_).pow((3, 2))
                        * (e__ + f__ * x_).sqrt()
                        * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                },
                rhs: {
                    let sub_guard = fresh_substitution_symbol().unwrap();
                    let sub_symbol = sub_guard.symbol();
                    let sub = Atom::var(sub_symbol);
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let bc_ad = &b__ * &c__ - &a__ * &d__;
                    let be_af = &b__ * &e__ - &a__ * &f__;
                    let bg_ah = &b__ * &g__ - &a__ * &h__;
                    let de_cf = &d__ * &e__ - &c__ * &f__;
                    let fg_eh = &f__ * &g__ - &e__ * &h__;
                    let transformed_integrand =
                        (Atom::num(1) + &bc_ad * sub.pow(2) / &de_cf).sqrt()
                            / (Atom::num(1) - &bg_ah * sub.pow(2) / &fg_eh).sqrt();
                    let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
                    let substitution = third.sqrt() / &first.sqrt();
                    let multiplier = -Atom::num(2)
                        * &second.sqrt()
                        * (-(&be_af * &fourth) / (&fg_eh * &first)).sqrt()
                        / (be_af
                            * fourth.sqrt()
                            * ((&b__ * &e__ - &a__ * &f__) * second / (de_cf * first)).sqrt());
                    let substituted = substitute_symbol(&transformed, sub_symbol, substitution);
                    rubi_star(multiplier, substituted)
                },
            ));
}

fn push_rules_rule_195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 195,
                source: "Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  b*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*e-a*f)*(b*g-a*h)) +
                  1/(2*(m+1)*(b*e-a*f)*(b*g-a*h)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
                    Simp[2*a*c*f*h*(m+1)-b*(d*e*g+c*(2*m+3)*(f*g+e*h))+2*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))*x-b*d*f*h*(2*m+5)*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LeQ[m,-2]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_4(symbols),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && leq!(m_, -2)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
                    let m_plus_1 = &m_ + Atom::num(1);
                    let be_af = &b__ * &e__ - &a__ * &f__;
                    let bg_ah = &b__ * &g__ - &a__ * &h__;
                    let denominator = &m_plus_1 * &be_af * &bg_ah;
                    let fg_eh = &f__ * &g__ + &e__ * &h__;
                    let simp = simp!(
                        Atom::num(2) * &a__ * &c__ * &f__ * &h__ * &m_plus_1
                            - &b__ * (&d__ * &e__ * &g__ + &c__ * (Atom::num(2) * &m_ + Atom::num(3)) * &fg_eh)
                            + Atom::num(2)
                                * (&a__ * &d__ * &f__ * &h__ * &m_plus_1
                                    - &b__ * (&m_ + Atom::num(2)) * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__))
                                * x_
                            - &b__ * &d__ * &f__ * &h__ * (Atom::num(2) * &m_ + Atom::num(5)) * x_.pow(2),
                        x_
                    );
                    let recursive = rubi_rhs_int(
                        &(first.pow(&m_plus_1) / &radical_product * simp),
                        x_,
                    );
                    rubi_simp(&(&b__ * first.pow(&m_plus_1) * &radical_product
                            / &denominator), x_)
                            + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
                },
            ));
}

fn push_rules_rule_196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 196,
        source: "Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[(e+f*x)^(p-1)*(g+h*x)^q/(a+b*x),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[(e+f*x)^(p-1)*(g+h*x)^q/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,q},x] && LtQ[0,p,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(p_) * (g__ + h__ * x_).pow(q_)
            / ((a__ + b__ * x_) * (c__ + d__ * x_)),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, q_], x_)
                && ltq!(0, p_, 1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let reduced = third.pow(p_ - Atom::num(1)) * fourth.pow(q_);
            let first_recursive = rubi_rhs_int(&(&reduced / first), x_);
            let second_recursive = rubi_rhs_int(&(reduced / second), x_);
            rubi_star((&b__ * &e__ - &a__ * &f__) / &determinant, first_recursive) - rubi_star((&d__ * &e__ - &c__ * &f__) / determinant, second_recursive)
        },
    ));
}

fn push_rules_rule_197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
                order: 197,
                source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_] :=
                  Int[ExpandIntegrand[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),(a+b*x)^m*(c+d*x)^(n+1/2),x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[m] && IntegerQ[n+1/2]",
                desc: "Expand the integrand and integrate the resulting terms.",
                refs: [],
                pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
                    / ((e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt()),
                with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_],
                optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                        && integerq!(m_)
                        && integerq!(&n_ + Atom::num(1) / Atom::num(2))
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let u = Atom::num(1) / (second.sqrt() * third.sqrt() * fourth.sqrt());
                    let expanded_factor =
                        first.pow(m_) * second.pow(&n_ + Atom::num(1) / Atom::num(2));
                    let expanded =
                        rubi_expand_integrand_product(&u, &expanded_factor, x_);
                    rubi_rhs_int(&expanded, x_)
                },
            ));
}

fn push_rules_rule_198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 198,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && IntegersQ[p,q]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && integersq!([p_, q_])
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_)
                * (c__ + d__ * x_).pow(n_)
                * (e__ + f__ * x_).pow(p_)
                * (g__ + h__ * x_).pow(q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 199,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_] :=
          h/b \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] +
          (b*g-a*h)/b \\[Star] Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && IGtQ[q,0] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_)
                && igtq!(q_, 0)
                && (sum_simplerq!(m_, 1)
                    || !sum_simplerq!(n_, 1) && !sum_simplerq!(p_, 1))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let q_minus_1 = &q_ - Atom::num(1);
            let first_recursive = rubi_rhs_int(
                &(first.pow(&m_ + Atom::num(1))
                    * second.pow(&n_)
                    * third.pow(&p_)
                    * fourth.pow(&q_minus_1)),
                x_,
            );
            let second_recursive = rubi_rhs_int(
                &(first.pow(m_)
                    * second.pow(n_)
                    * third.pow(p_)
                    * fourth.pow(q_minus_1)),
                x_,
            );
            rubi_star(&h__ / &b__, first_recursive)
                    + rubi_star((&b__ * &g__ - &a__ * &h__) / b__, second_recursive)
        },
    ));
}

fn push_rules_rule_200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 200,
        source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_] :=
          CannotIntegrate[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]",
        desc: "Leave the integral unevaluated because no applicable rule is known.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: { true },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_)
                * (c__ + d__ * x_).pow(n_)
                * (e__ + f__ * x_).pow(p_)
                * (g__ + h__ * x_).pow(q_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, u_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 201,
        source: "Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.*(e_.+f_.*u_)^p_.*(g_.+h_.*u_)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u_).pow(m_)
            * (c__ + d__ * u_).pow(n_)
            * (e__ + f__ * u_).pow(p_)
            * (g__ + h__ * u_).pow(q_),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, u_, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let (_, coefficient) = linear_coefficients(&u_, x_).rubi_rhs();
            let transformed_integrand = (&a__ + &b__ * &sub).pow(&m_)
                * (&c__ + &d__ * &sub).pow(&n_)
                * (&e__ + &f__ * &sub).pow(&p_)
                * (&g__ + &h__ * &sub).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = substitute_symbol(&transformed, sub_symbol, u_);
            rubi_star(Atom::num(1) / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, m_, n_, p_, q_, r_, x_, e__, f__, g__, h__, i__
    );
    rules.push(rubi_rule!(
                order: 202,
                source: "Int[(i_.*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_)^r_,x_Symbol] :=
                  (i*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q)^r/((a+b*x)^(m*r)*(c+d*x)^(n*r)*(e+f*x)^(p*r)*(g+h*x)^(q*r)) \\[Star]
                    Int[(a+b*x)^(m*r)*(c+d*x)^(n*r)*(e+f*x)^(p*r)*(g+h*x)^(q*r),x] /;
                FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p,q,r},x]",
                desc: "Piecewise constant extraction",
                refs: [],
                pattern: (i__ * (a__ + b__ * x_).pow(m_)
                    * (c__ + d__ * x_).pow(n_)
                    * (e__ + f__ * x_).pow(p_)
                    * (g__ + h__ * x_).pow(q_))
                .pow(r_),
                with: [i__, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, r_, x_],
                optional: [i__, a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, p_, q_, r_], x_)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let original = (&i__
                        * first.pow(&m_)
                        * second.pow(&n_)
                        * third.pow(&p_)
                        * fourth.pow(&q_))
                    .pow(&r_);
                    let transformed_integrand = first.pow(&m_ * &r_)
                        * second.pow(&n_ * &r_)
                        * third.pow(&p_ * &r_)
                        * fourth.pow(&q_ * &r_);
                    let recursive = rubi_rhs_int(&transformed_integrand, x_);
                    rubi_star(original / &transformed_integrand, recursive)
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
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_) * (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_)
        * (c__ + d__ * x_).pow(n_)
        * (e__ + f__ * x_).pow(p_)
        * (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_)
        * (c__ + d__ * x_).pow(n_)
        * (e__ + f__ * x_).pow(p_)
        * (g__ + h__ * x_).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_)
        * (c__ + d__ * x_).sqrt()
        * (e__ + f__ * x_).sqrt()
        * (g__ + h__ * x_).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).sqrt()
        / ((e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt()
        / (c__ + d__ * x_).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_)
        / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((a__ + b__ * x_)
            * (c__ + d__ * x_).sqrt()
            * (e__ + f__ * x_).sqrt()
            * (g__ + h__ * x_).sqrt())
}
