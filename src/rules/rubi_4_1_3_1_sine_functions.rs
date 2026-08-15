use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3445(rules);
    push_rules_rule_3446(rules);
    push_rules_rule_3447(rules);
    push_rules_rule_3448(rules);
    push_rules_rule_3449(rules);
    push_rules_rule_3450(rules);
    push_rules_rule_3451(rules);
    push_rules_rule_3452(rules);
    push_rules_rule_3453(rules);
    push_rules_rule_3454(rules);
    push_rules_rule_3455(rules);
    push_rules_rule_3456(rules);
    push_rules_rule_3457(rules);
    push_rules_rule_3458(rules);
    push_rules_rule_3459(rules);
    push_rules_rule_3460(rules);
    push_rules_rule_3461(rules);
    push_rules_rule_3462(rules);
    push_rules_rule_3463(rules);
    push_rules_rule_3464(rules);
    push_rules_rule_3465(rules);
    push_rules_rule_3466(rules);
    push_rules_rule_3467(rules);
    push_rules_rule_3468(rules);
    push_rules_rule_3469(rules);
    push_rules_rule_3470(rules);
    push_rules_rule_3471(rules);
    push_rules_rule_3472(rules);
    push_rules_rule_3473(rules);
    push_rules_rule_3474(rules);
    push_rules_rule_3475(rules);
    push_rules_rule_3476(rules);
    push_rules_rule_3477(rules);
    push_rules_rule_3478(rules);
    push_rules_rule_3479(rules);
    push_rules_rule_3480(rules);
    push_rules_rule_3481(rules);
    push_rules_rule_3482(rules);
    push_rules_rule_3483(rules);
    push_rules_rule_3484(rules);
    push_rules_rule_3485(rules);
    push_rules_rule_3486(rules);
    push_rules_rule_3487(rules);
    push_rules_rule_3488(rules);
}

fn push_rules_rule_3445(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3445,
        source: "Int[sin[e_.+f_.*x_]^n_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          Int[ExpandTrig[sin[e+f*x]^n*(a+b*sin[e+f*x])^m*(A+B*sin[e+f*x]),x],x] /;
        FreeQ[{a,b,e,f,A,B},x] && EqQ[A*b+a*B,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_)),
        with: [e__, f__, n_, a__, b__, m_, capital_a__, capital_b__, x_],
        optional: [e__, f__, n_, b__, m_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&capital_a__ * &b__ + &a__ * &capital_b__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = i_sin(&angle).pow(&n_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (&capital_a__ + &capital_b__ * i_sin(&angle));
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3446(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3446,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a^m*c^m \\[Star] Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m)*(A+B*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && Not[IntegerQ[n] && (LtQ[m,0] && GtQ[n,0] || LtQ[0,n,m] || LtQ[m,n,0])]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, m_, d__, n_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && !(integerq!(n_)
                    && (ltq!(m_, 0) && gtq!(n_, 0)
                        || ltq!(0, n_, m_)
                        || ltq!(m_, n_, 0)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &(angle.cos().pow(Atom::num(2) * &m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ - &m_)
                    * (&capital_a__ + &capital_b__ * angle.sin())),
                x_,
            );

            rubi_star(a__.pow(&m_) * c__.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_3447(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
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
        order: 3447,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m*(A*c+(B*c+A*d)*Sin[e+f*x]+B*d*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_))
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&capital_a__ * &c__
                        + (&capital_b__ * &c__ + &capital_a__ * &d__) * angle.sin()
                        + &capital_b__ * &d__ * angle.sin().pow(2))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3448(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3448,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          (A*b+a*B)/(2*a*b) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          (B*c+A*d)/(2*c*d) \\[Star] Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&c__ + &d__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).sqrt()),
                x_,
            );

            rubi_star((&capital_a__ * &b__ + &a__ * &capital_b__)
                        / (Atom::num(2) * &a__ * &b__), recursive1) + rubi_star((&capital_b__ * &c__ + &capital_a__ * &d__)
                        / (Atom::num(2) * &c__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3449(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3449,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[A*b*(m+n+1)+a*B*(m-n),0] && NeQ[m,-1/2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, d__, n_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&capital_a__ * &b__ * (&m_ + &n_ + 1) + &a__ * &capital_b__ * (&m_ - &n_), 0)
                && neq!(m_, -Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(-&capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (&m_ + &n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3450(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3450,
        source: "Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          B/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] -
          (B*c-A*d)/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star(&capital_b__ / &d__, recursive1)
                    - rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3451(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3451,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) +
          (a*B*(m-n)+A*b*(m+n+1))/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && (LtQ[m,-1/2] || ILtQ[m+n,0] && Not[SumSimplerQ[n,1]]) && NeQ[2*m+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, d__, n_, capital_a__, capital_b__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (ltq!(m_, minus_half) || iltq!(&m_ + &n_, 0) && !sum_simplerq!(n_, 1))
                && neq!(Atom::num(2) * &m_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_ + 1) * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_simp(&((&capital_a__ * &b__ - &a__ * &capital_b__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star((&a__ * &capital_b__ * (&m_ - &n_)
                            + &capital_a__ * &b__ * (&m_ + &n_ + 1))
                            / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3452(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3452,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) -
          (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]] && NeQ[m+n+1,0]",
        desc: "Algebraic expansion and doubly degenerate sine recurrence 1b with m\\[Rule]m+1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, d__, m_, capital_a__, capital_b__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, minus_half)
                && neq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_) * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_simp(&(-&capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (&m_ + &n_ + 1))), x_)
                    - rubi_star((&capital_b__ * &c__ * (&m_ - &n_)
                            - &capital_a__ * &d__ * (&m_ + &n_ + 1))
                            / (&d__ * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3453(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3453,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && EqQ[m+n+2,0] && EqQ[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1)),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(&m_ + &n_ + 2, 0)
                && eqq!(
                    &capital_a__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&n_ + 1))
                        - &capital_b__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1)),
                    0
                )
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&((&capital_b__ * &c__ - &capital_a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&f__ * (&n_ + 1) * (c__.pow(2) - d__.pow(2)))), x_)
        },
    ));
}

fn push_rules_rule_3454(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3454,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b^2*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) -
          b/(d*(n+1)*(b*c+a*d)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[a*A*d*(m-n-2)-B*(a*c*(m-1)+b*d*(n+1))-(A*b*d*(m+n+1)-B*(b*c*m-a*d*(n+1)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1/2] && LtQ[n,-1] &&
          IntegerQ[2*m] && (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 1a with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, Atom::num(1) / Atom::num(2))
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &a__ * &capital_a__ * &d__ * (&m_ - &n_ - 2)
                - &capital_b__ * (&a__ * &c__ * (&m_ - 1) + &b__ * &d__ * (&n_ + 1))
                - (&capital_a__ * &b__ * &d__ * (&m_ + &n_ + 1)
                    - &capital_b__ * (&b__ * &c__ * &m_ - &a__ * &d__ * (&n_ + 1)))
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-b__.pow(2)
                    * (&capital_b__ * &c__ - &capital_a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (&n_ + 1) * (&b__ * &c__ + &a__ * &d__))), x_)
                    - rubi_star(&b__ / (&d__ * (&n_ + 1) * (&b__ * &c__ + &a__ * &d__)), recursive)
        },
    ));
}

fn push_rules_rule_3455(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3455,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) +
          1/(d*(m+n+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
            Simp[a*A*d*(m+n+1)+B*(a*c*(m-1)+b*d*(n+1))+(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1/2] && Not[LtQ[n,-1]] && IntegerQ[2*m] &&
          (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, Atom::num(1) / Atom::num(2))
                && !ltq!(n_, -1)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &a__ * &capital_a__ * &d__ * (&m_ + &n_ + 1)
                + &capital_b__ * (&a__ * &c__ * (&m_ - 1) + &b__ * &d__ * (&n_ + 1))
                + (&capital_a__ * &b__ * &d__ * (&m_ + &n_ + 1)
                    - &capital_b__ * (&b__ * &c__ * &m_ - &a__ * &d__ * (Atom::num(2) * &m_ + &n_)))
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&b__
                    * &capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (&m_ + &n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3456(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3456,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) -
          1/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
            Simp[A*(a*d*n-b*c*(m+1))-B*(a*c*m+b*d*n)-d*(a*B*(m-n)+A*b*(m+n+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1/2] && GtQ[n,0] && IntegerQ[2*m] &&
          (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, minus_half)
                && gtq!(n_, 0)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &capital_a__ * (&a__ * &d__ * &n_ - &b__ * &c__ * (&m_ + 1))
                - &capital_b__ * (&a__ * &c__ * &m_ + &b__ * &d__ * &n_)
                - &d__ * (&a__ * &capital_b__ * (&m_ - &n_) + &capital_a__ * &b__ * (&m_ + &n_ + 1)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_ - 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&((&capital_a__ * &b__ - &a__ * &capital_b__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    - rubi_star(Atom::num(1) / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3457(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3457,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          b*(A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) +
          1/(a*(2*m+1)*(b*c-a*d)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[B*(a*c*m+b*d*(n+1))+A*(b*c*(m+1)-a*d*(2*m+n+2))+d*(A*b-a*B)*(m+n+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1/2] && Not[GtQ[n,0]] && IntegerQ[2*m] &&
          (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, minus_half)
                && !gtq!(n_, 0)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let simp_payload = &capital_b__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + &capital_a__ * (&b__ * &c__ * (&m_ + 1) - &a__ * &d__ * (Atom::num(2) * &m_ + &n_ + 2))
                + &d__ * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&m_ + &n_ + 2) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(&b__
                    * (&capital_a__ * &b__ - &a__ * &capital_b__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1) * &bc_minus_ad)), x_)
                    + rubi_star(Atom::num(1)
                            / (&a__ * (Atom::num(2) * &m_ + 1) * bc_minus_ad), recursive)
        },
    ));
}

fn push_rules_rule_3458(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3458,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && EqQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)),0]",
        desc: "Singly degenerate sine recurrence 1b with B\\[Rule]-A b (3+2 n)2 a (1+n),m\\[Rule]12,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(
                    &capital_a__ * &b__ * &d__ * (Atom::num(2) * &n_ + 3)
                        - &capital_b__ * (&b__ * &c__ - Atom::num(2) * &a__ * &d__ * (&n_ + 1)),
                    0
                )
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();

            rubi_simp(&(-Atom::num(2)
                    * &b__
                    * &capital_b__
                    * angle.cos()
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (Atom::num(2) * &n_ + 3) * (&a__ + &b__ * &sin).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3459(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3459,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b^2*(B*c-A*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]) +
          (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(2*d*(n+1)*(b*c+a*d)) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,-1]",
        desc: "Singly degenerate sine recurrence 1a with m\\[Rule]12,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin).pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&(-b__.pow(2)
                    * (&capital_b__ * &c__ - &capital_a__ * &d__)
                    * angle.cos()
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (&n_ + 1) * (&b__ * &c__ + &a__ * &d__) * (&a__ + &b__ * &sin).sqrt())), x_)
                    + rubi_star((&capital_a__ * &b__ * &d__ * (Atom::num(2) * &n_ + 3)
                            - &capital_b__
                                * (&b__ * &c__ - Atom::num(2) * &a__ * &d__ * (&n_ + 1)))
                            / (Atom::num(2)
                                * &d__
                                * (&n_ + 1)
                                * (&b__ * &c__ + &a__ * &d__)), recursive)
        },
    ));
}

fn push_rules_rule_3460(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3460,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) +
          (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(b*d*(2*n+3)) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[LtQ[n,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin).pow(&n_)),
                x_,
            );

            rubi_simp(&(-Atom::num(2)
                    * &b__
                    * &capital_b__
                    * angle.cos()
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (Atom::num(2) * &n_ + 3) * (&a__ + &b__ * &sin).sqrt())), x_)
                    + rubi_star((&capital_a__ * &b__ * &d__ * (Atom::num(2) * &n_ + 3)
                            - &capital_b__
                                * (&b__ * &c__ - Atom::num(2) * &a__ * &d__ * (&n_ + 1)))
                            / (&b__ * &d__ * (Atom::num(2) * &n_ + 3)), recursive)
        },
    ));
}

fn push_rules_rule_3461(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3461,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          (A*b-a*B)/b \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] +
          B/b \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );

            rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive1) + rubi_star(&capital_b__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3462(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3462,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) +
          1/(b*(m+n+1)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)*
            Simp[A*b*c*(m+n+1)+B*(a*c*m+b*d*n)+(A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[n,0] && (IntegerQ[n] || EqQ[m+1/2,0])",
        desc: "Singly degenerate sine recurrence 2c with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(n_, 0)
                && (integerq!(n_) || eqq!(&m_ + Atom::num(1) / Atom::num(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &capital_a__ * &b__ * &c__ * (&m_ + &n_ + 1)
                + &capital_b__ * (&a__ * &c__ * &m_ + &b__ * &d__ * &n_)
                + (&capital_a__ * &b__ * &d__ * (&m_ + &n_ + 1)
                    + &capital_b__ * (&a__ * &d__ * &m_ + &b__ * &c__ * &n_))
                    * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ - 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    / (&f__ * (&m_ + &n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3463(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3463,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) +
          1/(b*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
            Simp[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))+b*(B*c-A*d)*(m+n+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,-1] && (IntegerQ[n] || EqQ[m+1/2,0])",
        desc: "Singly degenerate sine recurrence 1c with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, -1)
                && (integerq!(n_) || eqq!(&m_ + Atom::num(1) / Atom::num(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &capital_a__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&n_ + 1))
                - &capital_b__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ + 1))
                + &b__ * (&capital_b__ * &c__ - &capital_a__ * &d__) * (&m_ + &n_ + 2) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&((&capital_b__ * &c__ - &capital_a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&f__ * (&n_ + 1) * (c__.pow(2) - d__.pow(2)))), x_)
                    + rubi_star(Atom::num(1)
                            / (&b__ * (&n_ + 1) * (c__.pow(2) - d__.pow(2))), recursive)
        },
    ));
}

fn push_rules_rule_3464(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3464,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          (A*b-a*B)/(b*c-a*d) \\[Star] Int[1/Sqrt[a+b*Sin[e+f*x]],x] +
          (B*c-A*d)/(b*c-a*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin())),
                x_,
            );

            rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__)
                        / (&b__ * &c__ - &a__ * &d__), recursive1) + rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__)
                        / (&b__ * &c__ - &a__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3465(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3465,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          B/d \\[Star] Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d \\[Star] Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && NeQ[m+1/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, c__, d__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && neq!(&m_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(&a__ + &b__ * angle.sin()).pow(&m_), x_);
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_) / (&c__ + &d__ * angle.sin())),
                x_,
            );

            rubi_star(&capital_b__ / &d__, recursive1)
                    - rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3466(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3466,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (A*b-a*B)/b \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] +
          B/b \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && NeQ[A*b+a*B,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, m_, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && neq!(&capital_a__ * &b__ + &a__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_) * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_ + 1) * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive1) + rubi_star(&capital_b__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3467(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3467,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^2*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (B*c-A*d)*(b*c-a*d)^2*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*d^2*(n+1)*(c^2-d^2)) -
          1/(d^2*(n+1)*(c^2-d^2)) \\[Star] Int[(c+d*Sin[e+f*x])^(n+1)*
            Simp[d*(n+1)*(B*(b*c-a*d)^2-A*d*(a^2*c+b^2*c-2*a*b*d))-
              ((B*c-A*d)*(a^2*d^2*(n+2)+b^2*(c^2+d^2*(n+1)))+2*a*b*d*(A*c*d*(n+2)-B*(c^2+d^2*(n+1))))*Sin[e+f*x]-
              b^2*B*d*(n+1)*(c^2-d^2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,-1]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]a A,B\\[Rule]A b+a B,C\\[Rule]b B,m\\[Rule]m-1,p\\[Rule]0",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(2)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let simp_payload = &d__
                * (&n_ + 1)
                * (&capital_b__ * bc_minus_ad.pow(2)
                    - &capital_a__
                        * &d__
                        * (a__.pow(2) * &c__ + b__.pow(2) * &c__ - Atom::num(2) * &a__ * &b__ * &d__))
                - ((&capital_b__ * &c__ - &capital_a__ * &d__)
                    * (a__.pow(2) * d__.pow(2) * (&n_ + 2)
                        + b__.pow(2) * (c__.pow(2) + d__.pow(2) * (&n_ + 1)))
                    + Atom::num(2)
                        * &a__
                        * &b__
                        * &d__
                        * (&capital_a__ * &c__ * &d__ * (&n_ + 2)
                            - &capital_b__ * (c__.pow(2) + d__.pow(2) * (&n_ + 1))))
                    * &sin
                - b__.pow(2) * &capital_b__ * &d__ * (&n_ + 1) * &c2_minus_d2 * sin.pow(2);
            let recursive =
                rubi_rhs_int(&((&c__ + &d__ * &sin).pow(&n_ + 1) * simp!(simp_payload, x_)), x_);

            rubi_simp(&((&capital_b__ * &c__ - &capital_a__ * &d__)
                    * bc_minus_ad.pow(2)
                    * angle.cos()
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&f__ * d__.pow(2) * (&n_ + 1) * &c2_minus_d2)), x_)
                    - rubi_star(Atom::num(1)
                            / (d__.pow(2) * (&n_ + 1) * c2_minus_d2), recursive)
        },
    ));
}

fn push_rules_rule_3468(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3468,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(b*c-a*d)*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[b*(b*c-a*d)*(B*c-A*d)*(m-1)+a*d*(a*A*c+b*B*c-(A*b+a*B)*d)*(n+1)+
              (b*(b*d*(B*c-A*d)+a*(A*c*d+B*(c^2-2*d^2)))*(n+1)-a*(b*c-a*d)*(B*c-A*d)*(n+2))*Sin[e+f*x]+
              b*(d*(A*b*c+a*B*c-a*A*d)*(m+n+1)-b*B*(c^2*m+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1] && LtQ[n,-1]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]a A,B\\[Rule]A b+a B,C\\[Rule]b B,m\\[Rule]m-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let c2_minus_d2 = c__.pow(2) - d__.pow(2);
            let simp_payload = &b__ * &bc_minus_ad * (&capital_b__ * &c__ - &capital_a__ * &d__) * (&m_ - 1)
                + &a__
                    * &d__
                    * (&a__ * &capital_a__ * &c__
                        + &b__ * &capital_b__ * &c__
                        - (&capital_a__ * &b__ + &a__ * &capital_b__) * &d__)
                    * (&n_ + 1)
                + (&b__
                    * (&b__ * &d__ * (&capital_b__ * &c__ - &capital_a__ * &d__)
                        + &a__
                            * (&capital_a__ * &c__ * &d__
                                + &capital_b__ * (c__.pow(2) - Atom::num(2) * d__.pow(2))))
                    * (&n_ + 1)
                    - &a__ * &bc_minus_ad * (&capital_b__ * &c__ - &capital_a__ * &d__) * (&n_ + 2))
                    * &sin
                + &b__
                    * (&d__
                        * (&capital_a__ * &b__ * &c__ + &a__ * &capital_b__ * &c__ - &a__ * &capital_a__ * &d__)
                        * (&m_ + &n_ + 1)
                        - &b__ * &capital_b__ * (c__.pow(2) * &m_ + d__.pow(2) * (&n_ + 1)))
                    * sin.pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 2)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&bc_minus_ad
                    * (&capital_b__ * &c__ - &capital_a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (&n_ + 1) * &c2_minus_d2)), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&n_ + 1) * c2_minus_d2), recursive)
        },
    ));
}

fn push_rules_rule_3469(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3469,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) +
          1/(d*(m+n+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
            Simp[a^2*A*d*(m+n+1)+b*B*(b*c*(m-1)+a*d*(n+1))+
              (a*d*(2*A*b+a*B)*(m+n+1)-b*B*(a*c-b*d*(m+n)))*Sin[e+f*x]+
              b*(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1] && Not[IGtQ[n,1] &&
          (Not[IntegerQ[m]] || EqQ[a,0] && NeQ[c,0])]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 1)
                && !(igtq!(n_, 1) && (!integerq!(m_) || eqq!(a__, 0) && neq!(c__, 0)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = a__.pow(2) * &capital_a__ * &d__ * (&m_ + &n_ + 1)
                + &b__ * &capital_b__ * (&b__ * &c__ * (&m_ - 1) + &a__ * &d__ * (&n_ + 1))
                + (&a__ * &d__ * (Atom::num(2) * &capital_a__ * &b__ + &a__ * &capital_b__) * (&m_ + &n_ + 1)
                    - &b__ * &capital_b__ * (&a__ * &c__ - &b__ * &d__ * (&m_ + &n_)))
                    * &sin
                + &b__
                    * (&capital_a__ * &b__ * &d__ * (&m_ + &n_ + 1)
                        - &capital_b__ * (&b__ * &c__ * &m_ - &a__ * &d__ * (Atom::num(2) * &m_ + &n_)))
                    * sin.pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ - 2)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&b__
                    * &capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ - 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&d__ * &f__ * (&m_ + &n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3470(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3470,
        source: "Int[Sqrt[c_+d_.*sin[e_.+f_.*x_]]*(A_.+B_.*sin[e_.+f_.*x_])/(b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          B*d/b^2 \\[Star] Int[Sqrt[b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          Int[(A*c+(B*c+A*d)*Sin[e+f*x])/((b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / (b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [c__, d__, e__, f__, capital_a__, capital_b__, b__, x_],
        optional: [d__, e__, f__, capital_a__, capital_b__, b__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 =
                rubi_rhs_int(&((&b__ * &sin).sqrt() / (&c__ + &d__ * &sin).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&capital_a__ * &c__ + (&capital_b__ * &c__ + &capital_a__ * &d__) * &sin)
                    / ((&b__ * &sin).pow(Atom::num(3) / Atom::num(2)) * (&c__ + &d__ * &sin).sqrt())),
                x_,
            );

            rubi_star(&capital_b__ * &d__ / b__.pow(2), recursive1) + recursive2
        },
    ));
}

fn push_rules_rule_3471(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3471,
        source: "Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]*(A_.+B_.*sin[e_.+f_.*x_])/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          B/b \\[Star] Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] +
          (A*b-a*B)/b \\[Star] Int[Sqrt[c+d*Sin[e+f*x]]/(a+b*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [c__, d__, e__, f__, capital_a__, capital_b__, a__, b__, x_],
        optional: [c__, d__, e__, f__, capital_a__, capital_b__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&c__ + &d__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&c__ + &d__ * angle.sin()).sqrt()
                    / (&a__ + &b__ * angle.sin()).pow(Atom::num(3) / Atom::num(2))),
                x_,
            );

            rubi_star(&capital_b__ / &b__, recursive1)
                    + rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3472(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3472,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2*(A*b-a*B)*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) +
          d/(a^2-b^2) \\[Star] Int[(A*b-a*B+(a*A-b*B)*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /;
        FreeQ[{a,b,d,e,f,A,B},x] && NeQ[a^2-b^2,0]",
        desc: "Nondegenerate sine recurrence 1a with c\\[Rule]0,C\\[Rule]0,m\\[Rule]-32,n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&capital_a__ * &b__ - &a__ * &capital_b__ + (&a__ * &capital_a__ - &b__ * &capital_b__) * &sin)
                    / ((&a__ + &b__ * &sin).sqrt() * (&d__ * &sin).pow(Atom::num(3) / Atom::num(2)))),
                x_,
            );

            rubi_simp(&(Atom::num(2) * (&capital_a__ * &b__ - &a__ * &capital_b__) * angle.cos()
                    / (&f__
                        * (a__.pow(2) - b__.pow(2))
                        * (&a__ + &b__ * &sin).sqrt()
                        * (&d__ * &sin).sqrt())), x_)
                    + rubi_star(&d__ / (a__.pow(2) - b__.pow(2)), recursive)
        },
    ));
}

fn push_rules_rule_3473(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_b__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3473,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*A*(c-d)*Tan[e+f*x]/(f*b*c^2)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
            EllipticE[ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
        FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2,0] && EqQ[A,B] && PosQ[(c+d)/b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_a_, capital_b__, e__, f__, b__, c__, d__, x_],
        optional: [capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a_, capital_b__], x_)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
                && posq!((&c__ + &d__) / &b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let csc = angle.csc();
            let rt = rubi_rt(&((&c__ + &d__) / &b__), 2);

            rubi_simp(&(-Atom::num(2)
                    * &capital_a_
                    * (&c__ - &d__)
                    * angle.tan()
                    * &rt
                    * (&c__ * (Atom::num(1) + &csc) / (&c__ - &d__)).sqrt()
                    * (&c__ * (Atom::num(1) - &csc) / (&c__ + &d__)).sqrt()
                    * rubi_elliptic_e(
                        ((&c__ + &d__ * &sin).sqrt() / ((&b__ * &sin).sqrt() * &rt)).asin(),
                        -(&c__ + &d__) / (&c__ - &d__),
                    )
                    / (&f__ * &b__ * c__.pow(2))), x_)
        },
    ));
}

fn push_rules_rule_3474(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_b__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3474,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -Sqrt[-b*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]] \\[Star] Int[(A+B*Sin[e+f*x])/((-b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2,0] && EqQ[A,B] && NegQ[(c+d)/b]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_a_, capital_b__, e__, f__, b__, c__, d__, x_],
        optional: [capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__, capital_a_, capital_b__], x_)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
                && negq!((&c__ + &d__) / &b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&capital_a_ + &capital_b__ * &sin)
                    / ((-&b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                        * (&c__ + &d__ * &sin).sqrt())),
                x_,
            );

            rubi_star(-(-&b__ * &sin).sqrt() / (&b__ * &sin).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3475(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3475,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*A*(c-d)*(a+b*Sin[e+f*x])/(f*(b*c-a*d)^2*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
            Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
            Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
            EllipticE[ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && EqQ[A,B] && PosQ[(a+b)/(c+d)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a_, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
                && posq!((&a__ + &b__) / (&c__ + &d__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let first = &a__ + &b__ * &sin;
            let second = &c__ + &d__ * &sin;
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let rt = rubi_rt(&((&a__ + &b__) / (&c__ + &d__)), 2);

            rubi_simp(&(-Atom::num(2)
                    * &capital_a_
                    * (&c__ - &d__)
                    * &first
                    * (&bc_minus_ad * (Atom::num(1) + &sin) / ((&c__ - &d__) * &first)).sqrt()
                    * (-&bc_minus_ad * (Atom::num(1) - &sin) / ((&c__ + &d__) * &first)).sqrt()
                    * rubi_elliptic_e(
                        (&rt * second.sqrt() / first.sqrt()).asin(),
                        (&a__ - &b__) * (&c__ + &d__) / ((&a__ + &b__) * (&c__ - &d__)),
                    )
                    / (&f__ * bc_minus_ad.pow(2) * &rt * angle.cos())), x_)
        },
    ));
}

fn push_rules_rule_3476(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3476,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]] \\[Star] Int[(A+B*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[-c-d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && EqQ[A,B] && NegQ[(a+b)/(c+d)]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a_, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_b__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
                && negq!((&a__ + &b__) / (&c__ + &d__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&capital_a_ + &capital_b__ * &sin)
                    / ((&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                        * (-&c__ - &d__ * &sin).sqrt())),
                x_,
            );

            rubi_star((-&c__ - &d__ * &sin).sqrt() / (&c__ + &d__ * &sin).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3477(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3477,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          (A-B)/(a-b) \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] -
          (A*b-a*B)/(a-b) \\[Star] Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && NeQ[A,B]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && neq!(capital_a__, capital_b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((Atom::num(1) + &sin)
                    / ((&a__ + &b__ * &sin).pow(Atom::num(3) / Atom::num(2))
                        * (&c__ + &d__ * &sin).sqrt())),
                x_,
            );

            rubi_star((&capital_a__ - &capital_b__) / (&a__ - &b__), recursive1) - rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / (&a__ - &b__), recursive2)
        },
    ));
}

fn push_rules_rule_3478(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3478,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (B*a-A*b)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) +
          1/((m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
            Simp[c*(a*A-b*B)*(m+1)+d*n*(A*b-a*B)+(d*(a*A-b*B)*(m+1)-c*(A*b-a*B)*(m+2))*Sin[e+f*x]-d*(A*b-a*B)*(m+n+2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && GtQ[n,0]",
        desc: "Nondegenerate sine recurrence 1a with C\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let simp_payload = &c__ * (&a__ * &capital_a__ - &b__ * &capital_b__) * (&m_ + 1)
                + &d__ * &n_ * (&capital_a__ * &b__ - &a__ * &capital_b__)
                + (&d__ * (&a__ * &capital_a__ - &b__ * &capital_b__) * (&m_ + 1)
                    - &c__ * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&m_ + 2))
                    * &sin
                - &d__ * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&m_ + &n_ + 2) * sin.pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_ - 1)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&((&capital_b__ * &a__ - &capital_a__ * &b__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    / (&f__ * (&m_ + 1) * &a2_minus_b2)), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3479(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3479,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(A*b^2-a*b*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(1+n)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) +
          1/((m+1)*(b*c-a*d)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[(a*A-b*B)*(b*c-a*d)*(m+1)+b*d*(A*b-a*B)*(m+n+2)+
              (A*b-a*B)*(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-
              b*d*(A*b-a*B)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && RationalQ[m] && m<-1 &&
          (EqQ[a,0] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && LtQ[n,-1] && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a,0])])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && rationalq!(m_)
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
            let simp_payload = (&a__ * &capital_a__ - &b__ * &capital_b__) * &bc_minus_ad * (&m_ + 1)
                + &b__ * &d__ * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&m_ + &n_ + 2)
                + (&capital_a__ * &b__ - &a__ * &capital_b__)
                    * (&a__ * &d__ * (&m_ + 1) - &b__ * &c__ * (&m_ + 2))
                    * &sin
                - &b__ * &d__ * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&m_ + &n_ + 3) * sin.pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_)
                    * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-(&capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&c__ + &d__ * &sin).pow(&n_ + 1)
                    / (&f__ * (&m_ + 1) * &bc_minus_ad * &a2_minus_b2)), x_)
                    + rubi_star(Atom::num(1)
                            / ((&m_ + 1) * bc_minus_ad * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3480(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3480,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          (A*b-a*B)/(b*c-a*d) \\[Star] Int[1/(a+b*Sin[e+f*x]),x] + (B*c-A*d)/(b*c-a*d) \\[Star] Int[1/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)) * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let recursive1 = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * &sin)), x_);
            let recursive2 = rubi_rhs_int(&(Atom::num(1) / (&c__ + &d__ * &sin)), x_);

            rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &bc_minus_ad, recursive1) + rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / bc_minus_ad, recursive2)
        },
    ));
}

fn push_rules_rule_3481(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3481,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          B/d \\[Star] Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d \\[Star] Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, c__, d__, x_],
        optional: [a__, b__, e__, f__, capital_a__, capital_b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(&((&a__ + &b__ * &sin).pow(&m_)), x_);
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) / (&c__ + &d__ * &sin)),
                x_,
            );

            rubi_star(&capital_b__ / &d__, recursive1)
                    - rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3482(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3482,
        source: "Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -2*B*Cos[e+f*x]*Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n/(f*(2*n+3)) +
          1/(2*n+3) \\[Star] Int[(c+d*Sin[e+f*x])^(n-1)/Sqrt[a+b*Sin[e+f*x]]*
            Simp[a*A*c*(2*n+3)+B*(b*c+2*a*d*n)+
              (B*(a*c+b*d)*(2*n+1)+A*(b*c+a*d)*(2*n+3))*Sin[e+f*x]+
              (A*b*d*(2*n+3)+B*(a*d+2*b*c*n))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && EqQ[n^2,1/4]",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]A c,B\\[Rule]B c+A d,C\\[Rule]B d,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && eqq!(n_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_n_plus_three = Atom::num(2) * &n_ + 3;
            let simp_payload = &a__ * &capital_a__ * &c__ * &two_n_plus_three
                + &capital_b__ * (&b__ * &c__ + Atom::num(2) * &a__ * &d__ * &n_)
                + (&capital_b__ * (&a__ * &c__ + &b__ * &d__) * (Atom::num(2) * &n_ + 1)
                    + &capital_a__ * (&b__ * &c__ + &a__ * &d__) * &two_n_plus_three)
                    * &sin
                + (&capital_a__ * &b__ * &d__ * &two_n_plus_three
                    + &capital_b__ * (&a__ * &d__ + Atom::num(2) * &b__ * &c__ * &n_))
                    * sin.pow(2);
            let recursive = rubi_rhs_int(
                &((&c__ + &d__ * &sin).pow(&n_ - 1)
                    * simp!(simp_payload, x_)
                    / (&a__ + &b__ * &sin).sqrt()),
                x_,
            );

            rubi_simp(&(-Atom::num(2)
                    * &capital_b__
                    * angle.cos()
                    * (&a__ + &b__ * &sin).sqrt()
                    * (&c__ + &d__ * &sin).pow(n_)
                    / (&f__ * &two_n_plus_three)), x_)
                    + rubi_star(Atom::num(1) / two_n_plus_three, recursive)
        },
    ));
}

fn push_rules_rule_3483(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_b__, a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3483,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          4*A/(f*Sqrt[a+b])*EllipticPi[-1,-ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
        FreeQ[{a,b,e,f,A,B},x] && GtQ[b,0] && GtQ[b^2-a^2,0] && EqQ[A,B]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a_ + capital_b__ * i_sin(e__ + f__ * x_))
            / (i_sin(e__ + f__ * x_).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a_, capital_b__, e__, f__, a__, b__, x_],
        optional: [capital_b__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a_, capital_b__], x_)
                && gtq!(b__, 0)
                && gtq!(b__.pow(2) - a__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();

            rubi_simp(&(Atom::num(4)
                    * &capital_a_
                    * rubi_elliptic_pi(
                        -Atom::num(1),
                        -(angle.cos() / (Atom::num(1) + &sin)).asin(),
                        -(&a__ - &b__) / (&a__ + &b__),
                    )
                    / (&f__ * (&a__ + &b__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3484(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_b__, a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3484,
        source: "Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]] \\[Star] Int[(A+B*Sin[e+f*x])/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,e,f,d,A,B},x] && GtQ[b,0] && GtQ[b^2-a^2,0] && EqQ[A,B]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (capital_a_ + capital_b__ * i_sin(e__ + f__ * x_))
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [capital_a_, capital_b__, e__, f__, a__, b__, d__, x_],
        optional: [capital_b__, e__, f__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, capital_a_, capital_b__], x_)
                && gtq!(b__, 0)
                && gtq!(b__.pow(2) - a__.pow(2), 0)
                && eqq!(capital_a_, capital_b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&capital_a_ + &capital_b__ * &sin) / (sin.sqrt() * (&a__ + &b__ * &sin).sqrt())),
                x_,
            );

            rubi_star(sin.sqrt() / (&d__ * &sin).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3485(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3485,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          B/d \\[Star] Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] -
          (B*c-A*d)/d \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, e__, f__, a__, b__, c__, d__, x_],
        optional: [capital_a__, capital_b__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(
                &((&c__ + &d__ * &sin).sqrt() / (&a__ + &b__ * &sin).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin).sqrt())),
                x_,
            );

            rubi_star(&capital_b__ / &d__, recursive1)
                    - rubi_star((&capital_b__ * &c__ - &capital_a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3486(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
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
        order: 3486,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
          Unintegrable[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, c__, d__, n_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            rubi_unintegrable(
                (&a__ + &b__ * angle.sin()).pow(m_)
                    * (&c__ + &d__ * angle.sin()).pow(n_)
                    * (&capital_a__ + &capital_b__ * angle.sin()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3487(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
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
        order: 3487,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_])^p_,x_Symbol] :=
          Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/(f*Cos[e+f*x]) \\[Star]
            Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2)*(A+B*x)^p,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_)).pow(p_),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, p_, x_],
        optional: [b__, e__, f__, m_, d__, n_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_ - Atom::num(1) / Atom::num(2))
                * (&capital_a__ + &capital_b__ * &z).pow(p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();

            rubi_star((&a__ + &b__ * &sin).sqrt() * (&c__ + &d__ * &sin).sqrt()
                    / (&f__ * angle.cos()), rubi_subst(&primitive, sub, sin))
        },
    ));
}

fn push_rules_rule_3488(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
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
        order: 3488,
        source: "Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_])^p_,x_Symbol] :=
          -Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]/(f*Sin[e+f*x]) \\[Star]
            Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2)*(A+B*x)^p,x],x,Cos[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_cos(e__ + f__ * x_)).pow(p_),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, p_, x_],
        optional: [b__, e__, f__, m_, d__, n_, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_ - Atom::num(1) / Atom::num(2))
                * (&capital_a__ + &capital_b__ * &z).pow(p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();

            rubi_star(-(&a__ + &b__ * &cos).sqrt() * (&c__ + &d__ * &cos).sqrt()
                    / (&f__ * angle.sin()), rubi_subst(&primitive, sub, cos))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3445_through_3488_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3445..=3488).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3445..=3488).collect::<Vec<_>>());
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
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
        / (c__ + d__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a_ = symbols.capital_a_;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (capital_a_ + capital_b__ * i_sin(e__ + f__ * x_))
        / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a_ = symbols.capital_a_;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (capital_a_ + capital_b__ * i_sin(e__ + f__ * x_))
        / ((b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_))
        / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}
