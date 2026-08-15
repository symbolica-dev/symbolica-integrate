use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3508(rules);
    push_rules_rule_3509(rules);
    push_rules_rule_3510(rules);
    push_rules_rule_3511(rules);
    push_rules_rule_3512(rules);
    push_rules_rule_3513(rules);
    push_rules_rule_3514(rules);
    push_rules_rule_3515(rules);
    push_rules_rule_3516(rules);
    push_rules_rule_3517(rules);
    push_rules_rule_3518(rules);
    push_rules_rule_3519(rules);
    push_rules_rule_3520(rules);
    push_rules_rule_3521(rules);
    push_rules_rule_3522(rules);
    push_rules_rule_3523(rules);
    push_rules_rule_3524(rules);
    push_rules_rule_3525(rules);
    push_rules_rule_3526(rules);
    push_rules_rule_3527(rules);
    push_rules_rule_3528(rules);
    push_rules_rule_3529(rules);
    push_rules_rule_3530(rules);
    push_rules_rule_3531(rules);
    push_rules_rule_3532(rules);
    push_rules_rule_3533(rules);
    push_rules_rule_3534(rules);
    push_rules_rule_3535(rules);
    push_rules_rule_3536(rules);
    push_rules_rule_3537(rules);
    push_rules_rule_3538(rules);
    push_rules_rule_3539(rules);
    push_rules_rule_3540(rules);
    push_rules_rule_3541(rules);
    push_rules_rule_3542(rules);
    push_rules_rule_3543(rules);
    push_rules_rule_3544(rules);
    push_rules_rule_3545(rules);
    push_rules_rule_3546(rules);
    push_rules_rule_3547(rules);
    push_rules_rule_3548(rules);
    push_rules_rule_3549(rules);
}

fn push_rules_rule_3508(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3508,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          1/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*(b*B-a*C+b*C*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NeQ[b*c-a*d,0] && EqQ[A*b^2-a*b*B+a^2*C,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    &capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__,
                    0
                )
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&b__ * &capital_b__ - &a__ * &capital_c__ + &b__ * &capital_c__ * &sin)),
                x_,
            );

            rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3509(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3509,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NeQ[b*c-a*d,0] && EqQ[A*b^2+a^2*C,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&a__ - &b__ * &sin)),
                x_,
            );

            rubi_star(-&capital_c__ / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3510(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3510,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(b*c-a*d)*(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) -
          1/(b^2*(m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*
            Simp[b*(m+1)*((b*B-a*C)*(b*c-a*d)-A*b*(a*c-b*d))+
              (b*B*(a^2*d+b^2*d*(m+1)-a*b*c*(m+2))+(b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]-
              b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && LtQ[m,-1]",
        desc: "Algebraic expansion, nondegenerate sine recurrence 1c with c\\[Rule]1,d\\[Rule]0,A\\[Rule]c,B\\[Rule]d,C\\[Rule]0,n\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__;
            let simp_payload = &b__
                * (&m_ + 1)
                * ((&b__ * &capital_b__ - &a__ * &capital_c__) * &bc_minus_ad
                    - &capital_a__ * &b__ * (&a__ * &c__ - &b__ * &d__))
                + (&b__ * &capital_b__ * (a__.pow(2) * &d__ + b__.pow(2) * &d__ * (&m_ + 1) - &a__ * &b__ * &c__ * (&m_ + 2))
                    + &bc_minus_ad * (&capital_a__ * b__.pow(2) * (&m_ + 2) + &capital_c__ * (a__.pow(2) + b__.pow(2) * (&m_ + 1))))
                    * &sin
                - &b__ * &capital_c__ * &d__ * (&m_ + 1) * &a2_minus_b2 * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&bc_minus_ad
                    * balance
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (b__.pow(2) * &f__ * (&m_ + 1) * &a2_minus_b2)), x_)
                    - rubi_star(Atom::num(1) / (b__.pow(2) * (&m_ + 1) * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3511(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3511,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(b*c-a*d)*(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) +
          1/(b^2*(m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*
            Simp[b*(m+1)*(a*C*(b*c-a*d)+A*b*(a*c-b*d))-
              ((b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]+
              b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && LtQ[m,-1]",
        desc: "Algebraic expansion, nondegenerate sine recurrence 1c with c\\[Rule]1,d\\[Rule]0,A\\[Rule]c,B\\[Rule]d,C\\[Rule]0,n\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__;
            let simp_payload = &b__
                * (&m_ + 1)
                * (&a__ * &capital_c__ * &bc_minus_ad + &capital_a__ * &b__ * (&a__ * &c__ - &b__ * &d__))
                - (&bc_minus_ad * (&capital_a__ * b__.pow(2) * (&m_ + 2) + &capital_c__ * (a__.pow(2) + b__.pow(2) * (&m_ + 1)))) * &sin
                + &b__ * &capital_c__ * &d__ * (&m_ + 1) * &a2_minus_b2 * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&bc_minus_ad
                    * balance
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (b__.pow(2) * &f__ * (&m_ + 1) * &a2_minus_b2)), x_)
                    + rubi_star(Atom::num(1) / (b__.pow(2) * (&m_ + 1) * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3512(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3512,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) +
          1/(b*(m+3)) \\[Star] Int[(a+b*Sin[e+f*x])^m*
            Simp[a*C*d+A*b*c*(m+3)+b*(B*c*(m+3)+d*(C*(m+2)+A*(m+3)))*Sin[e+f*x]-(2*a*C*d-b*(c*C+B*d)*(m+3))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && Not[LtQ[m,-1]]",
        desc: "Algebraic expansion, nondegenerate sine recurrence 1b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]a c,B\\[Rule]b c+a d,C\\[Rule]b d,m\\[Rule]m+1,n\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, d__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &a__ * &capital_c__ * &d__
                + &capital_a__ * &b__ * &c__ * (&m_ + 3)
                + &b__ * (&capital_b__ * &c__ * (&m_ + 3) + &d__ * (&capital_c__ * (&m_ + 2) + &capital_a__ * (&m_ + 3))) * &sin
                - (Atom::num(2) * &a__ * &capital_c__ * &d__ - &b__ * (&c__ * &capital_c__ + &capital_b__ * &d__) * (&m_ + 3)) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__
                    * &d__
                    * angle.cos()
                    * &sin
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 3))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 3)), recursive)
        },
    ));
}

fn push_rules_rule_3513(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3513,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) +
          1/(b*(m+3)) \\[Star] Int[(a+b*Sin[e+f*x])^m*
            Simp[a*C*d+A*b*c*(m+3)+b*d*(C*(m+2)+A*(m+3))*Sin[e+f*x]-(2*a*C*d-b*c*C*(m+3))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && Not[LtQ[m,-1]]",
        desc: "Algebraic expansion, nondegenerate sine recurrence 1b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]a c,B\\[Rule]b c+a d,C\\[Rule]b d,m\\[Rule]m+1,n\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, d__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &a__ * &capital_c__ * &d__
                + &capital_a__ * &b__ * &c__ * (&m_ + 3)
                + &b__ * &d__ * (&capital_c__ * (&m_ + 2) + &capital_a__ * (&m_ + 3)) * &sin
                - (Atom::num(2) * &a__ * &capital_c__ * &d__ - &b__ * &c__ * &capital_c__ * (&m_ + 3)) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__
                    * &d__
                    * angle.cos()
                    * &sin
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 3))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 3)), recursive)
        },
    ));
}

fn push_rules_rule_3514(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3514,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(2*b*c*f*(2*m+1)) -
          1/(2*b*c*d*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[A*(c^2*(m+1)+d^2*(2*m+n+2))-B*c*d*(m-n-1)-C*(c^2*m-d^2*(n+1))+d*((A*c+B*d)*(m+n+2)-c*C*(3*m-n))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && (LtQ[m,-1/2] || EqQ[m+n+2,0] && NeQ[2*m+1,0])",
        desc: "Algebraic expansion, singly degenerate sine recurrence 2b with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (ltq!(m_, minus_half)
                    || eqq!(&m_ + &n_ + 2, 0) && neq!(Atom::num(2) * &m_ + 1, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let direct = (&a__ * &capital_a__ - &b__ * &capital_b__ + &a__ * &capital_c__)
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (Atom::num(2) * &b__ * &c__ * &f__ * &two_m_plus_one);
            let simp_payload = &capital_a__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (Atom::num(2) * &m_ + &n_ + 2))
                - &capital_b__ * &c__ * &d__ * (&m_ - &n_ - 1)
                - &capital_c__ * (c__.pow(2) * &m_ - d__.pow(2) * (&n_ + 1))
                + &d__ * ((&capital_a__ * &c__ + &capital_b__ * &d__) * (&m_ + &n_ + 2) - &c__ * &capital_c__ * (Atom::num(3) * &m_ - &n_)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(2) * &b__ * &c__ * &d__ * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3515(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3515,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (a*A+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(2*b*c*f*(2*m+1)) -
          1/(2*b*c*d*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[A*(c^2*(m+1)+d^2*(2*m+n+2))-C*(c^2*m-d^2*(n+1))+d*(A*c*(m+n+2)-c*C*(3*m-n))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && (LtQ[m,-1/2] || EqQ[m+n+2,0] && NeQ[2*m+1,0])",
        desc: "Algebraic expansion, singly degenerate sine recurrence 2b with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (ltq!(m_, minus_half)
                    || eqq!(&m_ + &n_ + 2, 0) && neq!(Atom::num(2) * &m_ + 1, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let direct = (&a__ * &capital_a__ + &a__ * &capital_c__)
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (Atom::num(2) * &b__ * &c__ * &f__ * &two_m_plus_one);
            let simp_payload = &capital_a__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (Atom::num(2) * &m_ + &n_ + 2))
                - &capital_c__ * (c__.pow(2) * &m_ - d__.pow(2) * (&n_ + 1))
                + &d__ * (&capital_a__ * &c__ * (&m_ + &n_ + 2) - &c__ * &capital_c__ * (Atom::num(3) * &m_ - &n_)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(2) * &b__ * &c__ * &d__ * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3516(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3516,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) +
          Int[(a+b*Sin[e+f*x])^m*Simp[A+C+B*Sin[e+f*x],x]/Sqrt[c+d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]]",
        desc: "Algebraic expansion and doubly degenerate sine recurrence 2b with n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (capital_a__
                + capital_b__ * i_sin(e__ + f__ * x_)
                + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, c__, d__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, c__, d__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, minus_half)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_three = Atom::num(2) * &m_ + 3;
            let recursive = rubi_rhs_int(
                &(((&a__ + &b__ * &sin).pow(&m_)
                    * simp!(&capital_a__ + &capital_c__ + &capital_b__ * &sin, x_))
                    / (&c__ + &d__ * &sin).sqrt()),
                x_,
            );

            rubi_simp(&(-Atom::num(2) * &capital_c__ * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * two_m_plus_three * (&c__ + &d__ * &sin).sqrt())), x_)
                    + recursive
        },
    ));
}

fn push_rules_rule_3517(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3517,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) +
          (A+C) \\[Star] Int[(a+b*Sin[e+f*x])^m/Sqrt[c+d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]]",
        desc: "Algebraic expansion and doubly degenerate sine recurrence 2b with n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, c__, d__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_c__, c__, d__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, minus_half)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_three = Atom::num(2) * &m_ + 3;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) / (&c__ + &d__ * &sin).sqrt()),
                x_,
            );

            rubi_simp(&(-Atom::num(2) * &capital_c__ * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * two_m_plus_three * (&c__ + &d__ * &sin).sqrt())), x_)
                    + rubi_star(&capital_a__ + &capital_c__, recursive)
        },
    ));
}

fn push_rules_rule_3518(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3518,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(b*d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
            Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(b*B*d*(m+n+2)-b*c*C*(2*m+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]] && NeQ[m+n+2,0]",
        desc: "Algebraic expansion and singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n+1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && neq!(&m_ + &n_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &capital_a__ * &b__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + (&b__ * &capital_b__ * &d__ * &m_plus_n_plus_two - &b__ * &c__ * &capital_c__ * (Atom::num(2) * &m_ + 1)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3519(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3519,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(b*d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
            Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))-b*c*C*(2*m+1)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]] && NeQ[m+n+2,0]",
        desc: "Algebraic expansion and singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n+1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && neq!(&m_ + &n_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &capital_a__ * &b__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                - &b__ * &c__ * &capital_c__ * (Atom::num(2) * &m_ + 1) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3520(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3520,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) +
          1/(b*(b*c-a*d)*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
              (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1/2]",
        desc: "Algebraic expansion, singly degenerate sine recurrence 2b with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, minus_half)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let direct = (&a__ * &capital_a__ - &b__ * &capital_b__ + &a__ * &capital_c__)
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&f__ * &bc_minus_ad * &two_m_plus_one);
            let simp_payload = &capital_a__
                * (&a__ * &c__ * (&m_ + 1) - &b__ * &d__ * (Atom::num(2) * &m_ + &n_ + 2))
                + &capital_b__ * (&b__ * &c__ * &m_ + &a__ * &d__ * (&n_ + 1))
                - &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + (&d__ * (&a__ * &capital_a__ - &b__ * &capital_b__) * (&m_ + &n_ + 2)
                    + &capital_c__ * (&b__ * &c__ * (Atom::num(2) * &m_ + 1) - &a__ * &d__ * (&m_ - &n_ - 1)))
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * bc_minus_ad * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3521(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3521,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          a*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) +
          1/(b*(b*c-a*d)*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
              (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1/2]",
        desc: "Algebraic expansion, singly degenerate sine recurrence 2b with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, minus_half)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let direct = &a__
                * (&capital_a__ + &capital_c__)
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&f__ * &bc_minus_ad * &two_m_plus_one);
            let simp_payload = &capital_a__
                * (&a__ * &c__ * (&m_ + 1) - &b__ * &d__ * (Atom::num(2) * &m_ + &n_ + 2))
                - &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + (&a__ * &capital_a__ * &d__ * (&m_ + &n_ + 2)
                    + &capital_c__ * (&b__ * &c__ * (Atom::num(2) * &m_ + 1) - &a__ * &d__ * (&m_ - &n_ - 1)))
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * bc_minus_ad * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3522(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3522,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(b*d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
            Simp[A*d*(a*d*m+b*c*(n+1))+(c*C-B*d)*(a*c*m+b*d*(n+1))+b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[LtQ[m,-1/2]] && (LtQ[n,-1] || EqQ[m+n+2,0])",
        desc: "Algebraic expansion and singly degenerate sine recurrence 1c with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, capital_a__, capital_b__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && (ltq!(n_, -1) || eqq!(&m_ + &n_ + 2, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let direct = -(c__.pow(2) * &capital_c__ - &capital_b__ * &c__ * &d__ + &capital_a__ * d__.pow(2))
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * (&n_ + 1) * &c2_minus_d2);
            let simp_payload = &capital_a__ * &d__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&n_ + 1))
                + (&c__ * &capital_c__ - &capital_b__ * &d__) * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + &b__ * (&d__ * (&capital_b__ * &c__ - &capital_a__ * &d__) * (&m_ + &n_ + 2)
                    - &capital_c__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (&n_ + 1))) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_star(
                    Atom::num(1) / (&b__ * &d__ * (&n_ + 1) * c2_minus_d2),
                    recursive,
                ) + rubi_simp(&direct, x_)
        },
    ));
}

fn push_rules_rule_3523(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3523,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(b*d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
            Simp[A*d*(a*d*m+b*c*(n+1))+c*C*(a*c*m+b*d*(n+1))-b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[LtQ[m,-1/2]] && (LtQ[n,-1] || EqQ[m+n+2,0])",
        desc: "Algebraic expansion and singly degenerate sine recurrence 1c with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, capital_a__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && (ltq!(n_, -1) || eqq!(&m_ + &n_ + 2, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let direct = -(c__.pow(2) * &capital_c__ + &capital_a__ * d__.pow(2))
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * (&n_ + 1) * &c2_minus_d2);
            let simp_payload = &capital_a__ * &d__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&n_ + 1))
                + &c__ * &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                - &b__ * (&capital_a__ * d__.pow(2) * (&m_ + &n_ + 2)
                    + &capital_c__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (&n_ + 1))) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_star(
                    Atom::num(1) / (&b__ * &d__ * (&n_ + 1) * c2_minus_d2),
                    recursive,
                ) + rubi_simp(&direct, x_)
        },
    ));
}

fn push_rules_rule_3524(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3524,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(b*d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
            Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[LtQ[m,-1/2]] && NeQ[m+n+2,0]",
        desc: "Algebraic expansion and singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n+1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && neq!(&m_ + &n_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &capital_a__ * &b__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + (&capital_c__ * (&a__ * &d__ * &m_ - &b__ * &c__ * (&m_ + 1))
                    + &b__ * &capital_b__ * &d__ * &m_plus_n_plus_two)
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3525(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3525,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(b*d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
            Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[LtQ[m,-1/2]] && NeQ[m+n+2,0]",
        desc: "Algebraic expansion and singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n+1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);

            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && neq!(&m_ + &n_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &capital_a__ * &b__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + &capital_c__ * (&a__ * &d__ * &m_ - &b__ * &c__ * (&m_ + 1)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3526(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3526,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[A*d*(b*d*m+a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) -
              (d*(A*(a*d*(n+2)-b*c*(n+1))+B*(b*d*(n+1)-a*c*(n+2)))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] +
              b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,0] && LtQ[n,-1]",
        desc: "Nondegenerate sine recurrence 1a with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let direct = -(c__.pow(2) * &capital_c__ - &capital_b__ * &c__ * &d__ + &capital_a__ * d__.pow(2))
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * (&n_ + 1) * &c2_minus_d2);
            let simp_payload = &capital_a__ * &d__ * (&b__ * &d__ * &m_ + &a__ * &c__ * (&n_ + 1))
                + (&c__ * &capital_c__ - &capital_b__ * &d__) * (&b__ * &c__ * &m_ + &a__ * &d__ * (&n_ + 1))
                - (&d__ * (&capital_a__ * (&a__ * &d__ * (&n_ + 2) - &b__ * &c__ * (&n_ + 1))
                    + &capital_b__ * (&b__ * &d__ * (&n_ + 1) - &a__ * &c__ * (&n_ + 2)))
                    - &capital_c__ * (&b__ * &c__ * &d__ * (&n_ + 1) - &a__ * (c__.pow(2) + d__.pow(2) * (&n_ + 1))))
                    * &sin
                + &b__ * (&d__ * (&capital_b__ * &c__ - &capital_a__ * &d__) * (&m_ + &n_ + 2)
                    - &capital_c__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (&n_ + 1))) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&n_ + 1) * c2_minus_d2), recursive)
        },
    ));
}

fn push_rules_rule_3527(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3527,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[A*d*(b*d*m+a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) -
              (A*d*(a*d*(n+2)-b*c*(n+1))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] -
              b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,0] && LtQ[n,-1]",
        desc: "Nondegenerate sine recurrence 1a with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let direct = -(c__.pow(2) * &capital_c__ + &capital_a__ * d__.pow(2))
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * (&n_ + 1) * &c2_minus_d2);
            let simp_payload = &capital_a__ * &d__ * (&b__ * &d__ * &m_ + &a__ * &c__ * (&n_ + 1))
                + &c__ * &capital_c__ * (&b__ * &c__ * &m_ + &a__ * &d__ * (&n_ + 1))
                - (&capital_a__ * &d__ * (&a__ * &d__ * (&n_ + 2) - &b__ * &c__ * (&n_ + 1))
                    - &capital_c__ * (&b__ * &c__ * &d__ * (&n_ + 1) - &a__ * (c__.pow(2) + d__.pow(2) * (&n_ + 1))))
                    * &sin
                - &b__ * (&capital_a__ * d__.pow(2) * (&m_ + &n_ + 2)
                    + &capital_c__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (&n_ + 1))) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&n_ + 1) * c2_minus_d2), recursive)
        },
    ));
}

fn push_rules_rule_3528(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3528,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
            Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+
              (d*(A*b+a*B)*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+
              (C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,0] &&
          Not[IGtQ[n,0] && (Not[IntegerQ[m]] || EqQ[a,0] && NeQ[c,0])]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 0)
                && !(igtq!(n_, 0) && (!integerq!(m_) || eqq!(a__, 0) && neq!(c__, 0)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &a__ * &capital_a__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&b__ * &c__ * &m_ + &a__ * &d__ * (&n_ + 1))
                + (&d__ * (&capital_a__ * &b__ + &a__ * &capital_b__) * &m_plus_n_plus_two
                    - &capital_c__ * (&a__ * &c__ - &b__ * &d__ * (&m_ + &n_ + 1)))
                    * &sin
                + (&capital_c__ * (&a__ * &d__ * &m_ - &b__ * &c__ * (&m_ + 1))
                    + &b__ * &capital_b__ * &d__ * &m_plus_n_plus_two)
                    * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3529(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3529,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) +
          1/(d*(m+n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
            Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+(A*b*d*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+C*(a*d*m-b*c*(m+1))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,0] &&
          Not[IGtQ[n,0] && (Not[IntegerQ[m]] || EqQ[a,0] && NeQ[c,0])]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 0)
                && !(igtq!(n_, 0) && (!integerq!(m_) || eqq!(a__, 0) && neq!(c__, 0)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let m_plus_n_plus_two = &m_ + &n_ + 2;
            let direct = -&capital_c__
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&d__ * &f__ * &m_plus_n_plus_two);
            let simp_payload = &a__ * &capital_a__ * &d__ * &m_plus_n_plus_two
                + &capital_c__ * (&b__ * &c__ * &m_ + &a__ * &d__ * (&n_ + 1))
                + (&capital_a__ * &b__ * &d__ * &m_plus_n_plus_two
                    - &capital_c__ * (&a__ * &c__ - &b__ * &d__ * (&m_ + &n_ + 1)))
                    * &sin
                + &capital_c__ * (&a__ * &d__ * &m_ - &b__ * &c__ * (&m_ + 1)) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&d__ * m_plus_n_plus_two), recursive)
        },
    ));
}

fn push_rules_rule_3530(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        d__,
        e__,
        f__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3530,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          C/(b*d) \\[Star] Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] +
          1/b \\[Star] Int[(A*b+(b*B-a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, d__, x_],
        optional: [capital_a__, capital_b__, capital_c__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let denominator =
                (&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2)) * (&d__ * &sin).sqrt();
            let recursive1 =
                rubi_rhs_int(&((&d__ * &sin).sqrt() / (&a__ + &b__ * &sin).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&capital_a__ * &b__ + (&b__ * &capital_b__ - &a__ * &capital_c__) * &sin)
                    / denominator),
                x_,
            );

            rubi_star(&capital_c__ / (&b__ * &d__), recursive1)
                    + rubi_star(Atom::num(1) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3531(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3531,
        source: "Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          C/(b*d) \\[Star] Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] +
          1/b \\[Star] Int[(A*b-a*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_c__, e__, f__, a__, b__, d__, x_],
        optional: [capital_a__, capital_c__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let denominator =
                (&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2)) * (&d__ * &sin).sqrt();
            let recursive1 =
                rubi_rhs_int(&((&d__ * &sin).sqrt() / (&a__ + &b__ * &sin).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&capital_a__ * &b__ - &a__ * &capital_c__ * &sin) / denominator),
                x_,
            );

            rubi_star(&capital_c__ / (&b__ * &d__), recursive1)
                    + rubi_star(Atom::num(1) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3532(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3532,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          C/b^2 \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          1/b^2 \\[Star] Int[(A*b^2-a^2*C+b*(b*B-2*a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let denominator = (&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                * (&c__ + &d__ * &sin).sqrt();
            let recursive1 =
                rubi_rhs_int(&((&a__ + &b__ * &sin).sqrt() / (&c__ + &d__ * &sin).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&capital_a__ * b__.pow(2) - a__.pow(2) * &capital_c__
                    + &b__ * (&b__ * &capital_b__ - Atom::num(2) * &a__ * &capital_c__) * &sin)
                    / denominator),
                x_,
            );

            rubi_star(&capital_c__ / b__.pow(2), recursive1)
                    + rubi_star(Atom::num(1) / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3533(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3533,
        source: "Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          C/b^2 \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          1/b^2 \\[Star] Int[(A*b^2-a^2*C-2*a*b*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let denominator = (&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                * (&c__ + &d__ * &sin).sqrt();
            let recursive1 =
                rubi_rhs_int(&((&a__ + &b__ * &sin).sqrt() / (&c__ + &d__ * &sin).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&capital_a__ * b__.pow(2) - a__.pow(2) * &capital_c__
                    - Atom::num(2) * &a__ * &b__ * &capital_c__ * &sin)
                    / denominator),
                x_,
            );

            rubi_star(&capital_c__ / b__.pow(2), recursive1)
                    + rubi_star(Atom::num(1) / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3534(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3534,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) +
          1/((m+1)*(b*c-a*d)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[(m+1)*(b*c-a*d)*(a*A-b*B+a*C)+d*(A*b^2-a*b*B+a^2*C)*(m+n+2) -
              (c*(A*b^2-a*b*B+a^2*C)+(m+1)*(b*c-a*d)*(A*b-a*B+b*C))*Sin[e+f*x] -
              d*(A*b^2-a*b*B+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] &&
          (EqQ[a,0] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && LtQ[n,-1] && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a,0])])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && (eqq!(a__, 0) && integerq!(m_) && !integerq!(n_)
                    || !(integerq!(Atom::num(2) * &n_)
                        && ltq!(n_, -1)
                        && (integerq!(n_) && !integerq!(m_) || eqq!(a__, 0))))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__;
            let direct = -&balance
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_ + 1)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&f__ * (&m_ + 1) * &bc_minus_ad * &a2_minus_b2);
            let simp_payload = (&m_ + 1) * &bc_minus_ad * (&a__ * &capital_a__ - &b__ * &capital_b__ + &a__ * &capital_c__)
                + &d__ * &balance * (&m_ + &n_ + 2)
                - (&c__ * &balance + (&m_ + 1) * &bc_minus_ad * (&capital_a__ * &b__ - &a__ * &capital_b__ + &b__ * &capital_c__)) * &sin
                - &d__ * &balance * (&m_ + &n_ + 3) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * bc_minus_ad * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3535(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3535,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) +
          1/((m+1)*(b*c-a*d)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[a*(m+1)*(b*c-a*d)*(A+C)+d*(A*b^2+a^2*C)*(m+n+2) -
              (c*(A*b^2+a^2*C)+b*(m+1)*(b*c-a*d)*(A+C))*Sin[e+f*x] -
              d*(A*b^2+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] &&
          (EqQ[a,0] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && LtQ[n,-1] && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a,0])])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && (eqq!(a__, 0) && integerq!(m_) && !integerq!(n_)
                    || !(integerq!(Atom::num(2) * &n_)
                        && ltq!(n_, -1)
                        && (integerq!(n_) && !integerq!(m_) || eqq!(a__, 0))))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__;
            let direct = -&balance
                * angle.cos()
                * (&a__ + &b__ * &sin).pow(&m_ + 1)
                * (&c__ + &d__ * &sin).pow(&n_ + 1)
                / (&f__ * (&m_ + 1) * &bc_minus_ad * &a2_minus_b2);
            let simp_payload = &a__ * (&m_ + 1) * &bc_minus_ad * (&capital_a__ + &capital_c__)
                + &d__ * &balance * (&m_ + &n_ + 2)
                - (&c__ * &balance + &b__ * (&m_ + 1) * &bc_minus_ad * (&capital_a__ + &capital_c__)) * &sin
                - &d__ * &balance * (&m_ + &n_ + 3) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * bc_minus_ad * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3536(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3536,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          C*x/(b*d) +
          (A*b^2-a*b*B+a^2*C)/(b*(b*c-a*d)) \\[Star] Int[1/(a+b*Sin[e+f*x]),x] -
          (c^2*C-B*c*d+A*d^2)/(d*(b*c-a*d)) \\[Star] Int[1/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_))
                * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, capital_c__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let recursive1 = rubi_rhs_int(&(1 / (&a__ + &b__ * &sin)), x_);
            let recursive2 = rubi_rhs_int(&(1 / (&c__ + &d__ * &sin)), x_);

            rubi_simp(&(&capital_c__ * x_ / (&b__ * &d__)), x_)
                    + rubi_star((&capital_a__ * b__.pow(2)
                            - &a__ * &b__ * &capital_b__
                            + a__.pow(2) * &capital_c__)
                            / (&b__ * &bc_minus_ad), recursive1)
                    - rubi_star((c__.pow(2) * &capital_c__
                            - &capital_b__ * &c__ * &d__
                            + &capital_a__ * d__.pow(2))
                            / (&d__ * bc_minus_ad), recursive2)
        },
    ));
}

fn push_rules_rule_3537(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3537,
        source: "Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          C*x/(b*d) +
          (A*b^2+a^2*C)/(b*(b*c-a*d)) \\[Star] Int[1/(a+b*Sin[e+f*x]),x] -
          (c^2*C+A*d^2)/(d*(b*c-a*d)) \\[Star] Int[1/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_))
                * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_c__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let recursive1 = rubi_rhs_int(&(1 / (&a__ + &b__ * &sin)), x_);
            let recursive2 = rubi_rhs_int(&(1 / (&c__ + &d__ * &sin)), x_);

            rubi_simp(&(&capital_c__ * x_ / (&b__ * &d__)), x_)
                    + rubi_star((&capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__)
                            / (&b__ * &bc_minus_ad), recursive1)
                    - rubi_star((c__.pow(2) * &capital_c__ + &capital_a__ * d__.pow(2))
                            / (&d__ * bc_minus_ad), recursive2)
        },
    ));
}

fn push_rules_rule_3538(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3538,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          C/(b*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]],x] -
          1/(b*d) \\[Star] Int[Simp[a*c*C-A*b*d+(b*c*C-b*B*d+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
                * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(&((&a__ + &b__ * &sin).sqrt()), x_);
            let simp_payload = &a__ * &c__ * &capital_c__ - &capital_a__ * &b__ * &d__
                + (&b__ * &c__ * &capital_c__ - &b__ * &capital_b__ * &d__ + &a__ * &capital_c__ * &d__) * &sin;
            let recursive2 = rubi_rhs_int(
                &(simp!(simp_payload, x_)
                    / ((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin))),
                x_,
            );

            rubi_star(&capital_c__ / (&b__ * &d__), recursive1)
                    - rubi_star(Atom::num(1) / (&b__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3539(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3539,
        source: "Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          C/(b*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]],x] -
          1/(b*d) \\[Star] Int[Simp[a*c*C-A*b*d+(b*c*C+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
                * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(&((&a__ + &b__ * &sin).sqrt()), x_);
            let simp_payload = &a__ * &c__ * &capital_c__ - &capital_a__ * &b__ * &d__
                + (&b__ * &c__ * &capital_c__ + &a__ * &capital_c__ * &d__) * &sin;
            let recursive2 = rubi_rhs_int(
                &(simp!(simp_payload, x_)
                    / ((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin))),
                x_,
            );

            rubi_star(&capital_c__ / (&b__ * &d__), recursive1)
                    - rubi_star(Atom::num(1) / (&b__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3540(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3540,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) +
          1/(2*d) \\[Star] Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
            Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-d*(A*b+a*B))*Sin[e+f*x]+(2*b*B*d-C*(b*c+a*d))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Nondegenerate sine recurrence 1b with m\\[Rule]-12,n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, capital_c__, e__, f__, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = Atom::num(2) * &a__ * &capital_a__ * &d__
                - &capital_c__ * (&b__ * &c__ - &a__ * &d__)
                - Atom::num(2) * (&a__ * &c__ * &capital_c__ - &d__ * (&capital_a__ * &b__ + &a__ * &capital_b__)) * &sin
                + (Atom::num(2) * &b__ * &capital_b__ * &d__ - &capital_c__ * (&b__ * &c__ + &a__ * &d__))
                    * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((1 / ((&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                    * (&c__ + &d__ * &sin).sqrt()))
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__ * angle.cos() * (&c__ + &d__ * &sin).sqrt()
                    / (&d__ * &f__ * (&a__ + &b__ * &sin).sqrt())), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &d__), recursive)
        },
    ));
}

fn push_rules_rule_3541(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3541,
        source: "Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) +
          1/(2*d) \\[Star] Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
            Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-A*b*d)*Sin[e+f*x]-C*(b*c+a*d)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Nondegenerate sine recurrence 1b with m\\[Rule]-12,n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_c__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_c__, e__, f__, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = Atom::num(2) * &a__ * &capital_a__ * &d__
                - &capital_c__ * (&b__ * &c__ - &a__ * &d__)
                - Atom::num(2) * (&a__ * &c__ * &capital_c__ - &capital_a__ * &b__ * &d__) * &sin
                - &capital_c__ * (&b__ * &c__ + &a__ * &d__) * (&sin).pow(2);
            let recursive = rubi_rhs_int(
                &((1 / ((&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                    * (&c__ + &d__ * &sin).sqrt()))
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__ * angle.cos() * (&c__ + &d__ * &sin).sqrt()
                    / (&d__ * &f__ * (&a__ + &b__ * &sin).sqrt())), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &d__), recursive)
        },
    ));
}

fn push_rules_rule_3542(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3542,
        source: "Int[(d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (b*B-a*C)/b^2 \\[Star] Int[(d*Sin[e+f*x])^n,x] +
          C/(b*d) \\[Star] Int[(d*Sin[e+f*x])^(n+1),x] +
          (A*b^2-a*b*B+a^2*C)/b^2 \\[Star] Int[(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,A,B,C,n},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__
                + capital_b__ * i_sin(e__ + f__ * x_)
                + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [d__, e__, f__, n_, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [d__, e__, f__, n_, capital_a__, capital_b__, capital_c__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let powered = (&d__ * &sin).pow(&n_);
            let recursive1 = rubi_rhs_int(&powered, x_);
            let recursive2 = rubi_rhs_int(&((&d__ * &sin).pow(&n_ + 1)), x_);
            let recursive3 = rubi_rhs_int(&(powered / (&a__ + &b__ * &sin)), x_);

            rubi_star((&b__ * &capital_b__ - &a__ * &capital_c__) / b__.pow(2), recursive1) + rubi_star(&capital_c__ / (&b__ * &d__), recursive2) + rubi_star((&capital_a__ * b__.pow(2)
                        - &a__ * &b__ * &capital_b__
                        + a__.pow(2) * &capital_c__)
                        / b__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3543(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3543,
        source: "Int[(d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2)/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -a*C/b^2 \\[Star] Int[(d*Sin[e+f*x])^n,x] +
          C/(b*d) \\[Star] Int[(d*Sin[e+f*x])^(n+1),x] +
          (A*b^2+a^2*C)/b^2 \\[Star] Int[(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,A,C,n},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [d__, e__, f__, n_, capital_a__, capital_c__, a__, b__, x_],
        optional: [d__, e__, f__, n_, capital_a__, capital_c__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a__, capital_c__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let powered = (&d__ * &sin).pow(&n_);
            let recursive1 = rubi_rhs_int(&powered, x_);
            let recursive2 = rubi_rhs_int(&((&d__ * &sin).pow(&n_ + 1)), x_);
            let recursive3 = rubi_rhs_int(&(powered / (&a__ + &b__ * &sin)), x_);

            rubi_star(-&a__ * &capital_c__ / b__.pow(2), recursive1)
                    + rubi_star(&capital_c__ / (&b__ * &d__), recursive2)
                    + rubi_star((&capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__)
                            / b__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3544(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3544,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          Unintegrable[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();

            rubi_unintegrable(
                (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&capital_a__ + &capital_b__ * &sin + &capital_c__ * (&sin).pow(2)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3545(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3545,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          Unintegrable[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+C*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();

            rubi_unintegrable(
                (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&capital_a__ + &capital_c__ * (&sin).pow(2)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3546(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3546,
        source: "Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p) \\[Star] Int[(b*Sin[e+f*x])^(m*p)*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
        FreeQ[{b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_).pow(p_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__
                + capital_b__ * i_sin(e__ + f__ * x_)
                + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let mp = &m_ * &p_;
            let recursive = rubi_rhs_int(
                &((&b__ * &sin).pow(&mp)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&capital_a__ + &capital_b__ * &sin + &capital_c__ * (&sin).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&sin).pow(&p_)).pow(&m_) / (&b__ * &sin).pow(mp), recursive)
        },
    ));
}

fn push_rules_rule_3547(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3547,
        source: "Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p) \\[Star] Int[(b*Cos[e+f*x])^(m*p)*(c+d*Cos[e+f*x])^n*(A+B*Cos[e+f*x]+C*Cos[e+f*x]^2),x] /;
        FreeQ[{b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_cos(e__ + f__ * x_).pow(p_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__
                + capital_b__ * i_cos(e__ + f__ * x_)
                + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let mp = &m_ * &p_;
            let recursive = rubi_rhs_int(
                &((&b__ * &cos).pow(&mp)
                    * (&c__ + &d__ * &cos).pow(&n_)
                    * (&capital_a__ + &capital_b__ * &cos + &capital_c__ * (&cos).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&cos).pow(&p_)).pow(&m_) / (&b__ * &cos).pow(mp), recursive)
        },
    ));
}

fn push_rules_rule_3548(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_c__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3548,
        source: "Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p) \\[Star] Int[(b*Sin[e+f*x])^(m*p)*(c+d*Sin[e+f*x])^n*(A+C*Sin[e+f*x]^2),x] /;
        FreeQ[{b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_).pow(p_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_c__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let mp = &m_ * &p_;
            let recursive = rubi_rhs_int(
                &((&b__ * &sin).pow(&mp)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * (&capital_a__ + &capital_c__ * (&sin).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&sin).pow(&p_)).pow(&m_) / (&b__ * &sin).pow(mp), recursive)
        },
    ));
}

fn push_rules_rule_3549(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_c__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3549,
        source: "Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p) \\[Star] Int[(b*Cos[e+f*x])^(m*p)*(c+d*Cos[e+f*x])^n*(A+C*Cos[e+f*x]^2),x] /;
        FreeQ[{b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_cos(e__ + f__ * x_).pow(p_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, c__, d__, n_, capital_a__, capital_c__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let mp = &m_ * &p_;
            let recursive = rubi_rhs_int(
                &((&b__ * &cos).pow(&mp)
                    * (&c__ + &d__ * &cos).pow(&n_)
                    * (&capital_a__ + &capital_c__ * (&cos).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&cos).pow(&p_)).pow(&m_) / (&b__ * &cos).pow(mp), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3508_through_3542_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3508..=3542).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3508..=3542).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3543_through_3549_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3543..=3549).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3543..=3549).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_))
        * (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_))
        * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}
