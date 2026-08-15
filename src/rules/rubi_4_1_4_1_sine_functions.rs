use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3489(rules);
    push_rules_rule_3490(rules);
    push_rules_rule_3491(rules);
    push_rules_rule_3492(rules);
    push_rules_rule_3493(rules);
    push_rules_rule_3494(rules);
    push_rules_rule_3495(rules);
    push_rules_rule_3496(rules);
    push_rules_rule_3497(rules);
    push_rules_rule_3498(rules);
    push_rules_rule_3499(rules);
    push_rules_rule_3500(rules);
    push_rules_rule_3501(rules);
    push_rules_rule_3502(rules);
    push_rules_rule_3503(rules);
    push_rules_rule_3504(rules);
    push_rules_rule_3505(rules);
    push_rules_rule_3506(rules);
    push_rules_rule_3507(rules);
}

fn push_rules_rule_3489(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_b__, capital_c__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3489,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_.*(B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          1/b \\[Star] Int[(b*Sin[e+f*x])^(m+1)*(B+C*Sin[e+f*x]),x] /;
        FreeQ[{b,e,f,B,C,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (capital_b__ * i_sin(e__ + f__ * x_)
                + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, m_, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_b__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_b__, capital_c__, m_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&b__ * &sin).pow(&m_ + 1) * (&capital_b__ + &capital_c__ * &sin)),
                x_,
            );

            rubi_star(Atom::num(1) / &b__, recursive)
        },
    ));
}

fn push_rules_rule_3490(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_c__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3490,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          A*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) /;
        FreeQ[{b,e,f,A,C,m},x] && EqQ[A*(m+2)+C*(m+1),0]",
        desc: "Nondegenerate sine recurrence 1a with n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, e__, f__, m_, capital_a_, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a_, capital_c__, m_], x_)
                && eqq!(&capital_a_ * (&m_ + 2) + &capital_c__ * (&m_ + 1), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            rubi_simp(&(&capital_a_ * angle.cos() * (&b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3491(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_c__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3491,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          A*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) + (A*(m+2)+C*(m+1))/(b^2*(m+1)) \\[Star] Int[(b*Sin[e+f*x])^(m+2),x] /;
        FreeQ[{b,e,f,A,C},x] && LtQ[m,-1]",
        desc: "Nondegenerate sine recurrence 1a with n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, e__, f__, m_, capital_a_, capital_c__, x_],
        optional: [b__, e__, f__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a_, capital_c__], x_)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(&((&b__ * &sin).pow(&m_ + 2)), x_);

            rubi_simp(&(&capital_a_ * angle.cos() * (&b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star((&capital_a_ * (&m_ + 2)
                            + &capital_c__ * (&m_ + 1))
                            / (b__.pow(2) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3492(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_c__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3492,
        source: "Int[sin[e_.+f_.*x_]^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -1/f \\[Star] Subst[Int[(1-x^2)^((m-1)/2)*(A+C-C*x^2),x],x,Cos[e+f*x]] /;
        FreeQ[{e,f,A,C},x] && IGtQ[(m+1)/2,0]",
        desc: "Algebraic expansion and integration by substitution",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(m_)
            * (capital_a_ + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [e__, f__, m_, capital_a_, capital_c__, x_],
        optional: [e__, f__, m_, capital_c__],
        when: {
            freeq!([e__, f__, capital_a_, capital_c__], x_)
                && igtq!((&m_ + 1) / 2, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (Atom::num(1) - z.pow(2)).pow((&m_ - 1) / 2)
                * (&capital_a_ + &capital_c__ - &capital_c__ * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, angle.cos());
            rubi_star(-Atom::num(1) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3493(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a_, capital_c__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3493,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + (A*(m+2)+C*(m+1))/(m+2) \\[Star] Int[(b*Sin[e+f*x])^m,x] /;
        FreeQ[{b,e,f,A,C,m},x] && Not[LtQ[m,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, e__, f__, m_, capital_a_, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a_, capital_c__, m_], x_)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(&((&b__ * &sin).pow(&m_)), x_);

            rubi_simp(&(-&capital_c__ * angle.cos() * (&b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star((&capital_a_ * (&m_ + 2) + &capital_c__ * (&m_ + 1))
                            / (&m_ + 2), recursive)
        },
    ));
}

fn push_rules_rule_3494(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3494,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          1/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[A*b^2-a*b*B+a^2*C,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && eqq!(
                    &capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__,
                    0
                )
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &b__ * &capital_b__ - &a__ * &capital_c__ + &b__ * &capital_c__ * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3495(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3495,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          C/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[-a+b*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,C,m},x] && EqQ[A*b^2+a^2*C,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_c__, m_], x_)
                && eqq!(&capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(-&a__ + &b__ * &sin, x_)),
                x_,
            );

            rubi_star(&capital_c__ / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3496(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3496,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (A-C) \\[Star] Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x]),x] + C \\[Star] Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x])^2,x] /;
        FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[A-B+C,0] && Not[IntegerQ[2*m]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && eqq!(&capital_a__ - &capital_b__ + &capital_c__, 0)
                && !integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * (Atom::num(1) + &sin)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * (Atom::num(1) + &sin).pow(2)),
                x_,
            );

            rubi_star(&capital_a__ - &capital_c__, recursive1)
                    + rubi_star(capital_c__, recursive2)
        },
    ));
}

fn push_rules_rule_3497(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3497,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (A-C) \\[Star] Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x]),x] + C \\[Star] Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x])^2,x] /;
        FreeQ[{a,b,e,f,A,C,m},x] && EqQ[A+C,0] && Not[IntegerQ[2*m]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_c__, m_], x_)
                && eqq!(&capital_a__ + &capital_c__, 0)
                && !integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * (Atom::num(1) + &sin)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * (Atom::num(1) + &sin).pow(2)),
                x_,
            );

            rubi_star(&capital_a__ - &capital_c__, recursive1)
                    + rubi_star(capital_c__, recursive2)
        },
    ));
}

fn push_rules_rule_3498(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3498,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (A*b-a*B+b*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) +
          1/(a^2*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)+m*(b*B-a*C)+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,B,C},x] && LtQ[m,-1] && EqQ[a^2-b^2,0]",
        desc: "Symmetric sine recurrence 2a with m\\[Rule]0 plus rule for integrands of the form Sin[e+f x]2(a+b Sin[e+f x])mBold",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && ltq!(m_, -1)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let simp_payload = &a__ * &capital_a__ * (&m_ + 1)
                + &m_ * (&b__ * &capital_b__ - &a__ * &capital_c__)
                + &b__ * &capital_c__ * &two_m_plus_one * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&((&capital_a__ * &b__ - &a__ * &capital_b__ + &b__ * &capital_c__)
                    * angle.cos()
                    * (&a__ + &b__ * &sin).pow(&m_)
                    / (&a__ * &f__ * &two_m_plus_one)), x_)
                    + rubi_star(Atom::num(1) / (a__.pow(2) * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3499(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3499,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          b*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) +
          1/(a^2*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)-a*C*m+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,C},x] && LtQ[m,-1] && EqQ[a^2-b^2,0]",
        desc: "Symmetric sine recurrence 2a with m\\[Rule]0 plus rule for integrands of the form Sin[e+f x]2(a+b Sin[e+f x])mBold",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_c__], x_)
                && ltq!(m_, -1)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let two_m_plus_one = Atom::num(2) * &m_ + 1;
            let simp_payload = &a__ * &capital_a__ * (&m_ + 1)
                - &a__ * &capital_c__ * &m_
                + &b__ * &capital_c__ * &two_m_plus_one * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(&b__ * (&capital_a__ + &capital_c__) * angle.cos() * (&a__ + &b__ * &sin).pow(&m_)
                    / (&a__ * &f__ * &two_m_plus_one)), x_)
                    + rubi_star(Atom::num(1) / (a__.pow(2) * two_m_plus_one), recursive)
        },
    ));
}

fn push_rules_rule_3500(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3500,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) +
          1/(b*(m+1)*(a^2-b^2)) \\[Star]
            Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,B,C},x] && LtQ[m,-1] && NeQ[a^2-b^2,0]",
        desc: "Nondegenerate sine recurrence 1a with n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__], x_)
                && ltq!(m_, -1)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__;
            let simp_payload = &b__ * (&a__ * &capital_a__ - &b__ * &capital_b__ + &a__ * &capital_c__) * (&m_ + 1)
                - (&balance + &b__ * (&capital_a__ * &b__ - &a__ * &capital_b__ + &b__ * &capital_c__) * (&m_ + 1)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-balance * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1) * &a2_minus_b2)), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 1) * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3501(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3501,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) +
          1/(b*(m+1)*(a^2-b^2)) \\[Star]
            Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b^2*(A+C)*(m+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,C},x] && LtQ[m,-1] && NeQ[a^2-b^2,0]",
        desc: "Nondegenerate sine recurrence 1a with n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_c__], x_)
                && ltq!(m_, -1)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let a2_minus_b2 = a__.pow(2) - b__.pow(2);
            let balance = &capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__;
            let simp_payload = &a__ * &b__ * (&capital_a__ + &capital_c__) * (&m_ + 1)
                - (&balance + b__.pow(2) * (&capital_a__ + &capital_c__) * (&m_ + 1)) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_ + 1) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-balance * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1) * &a2_minus_b2)), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 1) * a2_minus_b2), recursive)
        },
    ));
}

fn push_rules_rule_3502(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        e__,
        f__,
        m_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3502,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) +
          1/(b*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,B,C,m},x] && Not[LtQ[m,-1]]",
        desc: "Nondegenerate sine recurrence 1b with m\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &capital_a__ * &b__ * (&m_ + 2)
                + &b__ * &capital_c__ * (&m_ + 1)
                + (&b__ * &capital_b__ * (&m_ + 2) - &a__ * &capital_c__) * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__ * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3503(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3503,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) +
          1/(b*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)-a*C*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,e,f,A,C,m},x] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, m_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_c__, m_], x_)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let simp_payload = &capital_a__ * &b__ * (&m_ + 2)
                + &b__ * &capital_c__ * (&m_ + 1)
                - &a__ * &capital_c__ * &sin;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * &sin).pow(&m_) * simp!(simp_payload, x_)),
                x_,
            );

            rubi_simp(&(-&capital_c__ * angle.cos() * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3504(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        b__,
        e__,
        f__,
        m_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3504,
        source: "Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p) \\[Star] Int[(b*Sin[e+f*x])^(m*p)*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
        FreeQ[{b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_).pow(p_)).pow(m_)
            * (capital_a__
                + capital_b__ * i_sin(e__ + f__ * x_)
                + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&b__ * &sin).pow(&m_ * &p_)
                    * (&capital_a__ + &capital_b__ * &sin + &capital_c__ * (&sin).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&sin).pow(&p_)).pow(&m_) / (&b__ * &sin).pow(&m_ * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3505(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        b__,
        e__,
        f__,
        m_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3505,
        source: "Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p) \\[Star] Int[(b*Cos[e+f*x])^(m*p)*(A+B*Cos[e+f*x]+C*Cos[e+f*x]^2),x] /;
        FreeQ[{b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_cos(e__ + f__ * x_).pow(p_)).pow(m_)
            * (capital_a__
                + capital_b__ * i_cos(e__ + f__ * x_)
                + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let recursive = rubi_rhs_int(
                &((&b__ * &cos).pow(&m_ * &p_)
                    * (&capital_a__ + &capital_b__ * &cos + &capital_c__ * (&cos).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&cos).pow(&p_)).pow(&m_) / (&b__ * &cos).pow(&m_ * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3506(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3506,
        source: "Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p) \\[Star] Int[(b*Sin[e+f*x])^(m*p)*(A+C*Sin[e+f*x]^2),x] /;
        FreeQ[{b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_).pow(p_)).pow(m_)
            * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a__, capital_c__, m_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive = rubi_rhs_int(
                &((&b__ * &sin).pow(&m_ * &p_) * (&capital_a__ + &capital_c__ * (&sin).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&sin).pow(&p_)).pow(&m_) / (&b__ * &sin).pow(&m_ * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3507(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3507,
        source: "Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
          (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p) \\[Star] Int[(b*Cos[e+f*x])^(m*p)*(A+C*Cos[e+f*x]^2),x] /;
        FreeQ[{b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_cos(e__ + f__ * x_).pow(p_)).pow(m_)
            * (capital_a__ + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        with: [b__, e__, f__, p_, m_, capital_a__, capital_c__, x_],
        optional: [b__, e__, f__, capital_a__, capital_c__],
        when: {
            freeq!([b__, e__, f__, capital_a__, capital_c__, m_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let recursive = rubi_rhs_int(
                &((&b__ * &cos).pow(&m_ * &p_) * (&capital_a__ + &capital_c__ * (&cos).pow(2))),
                x_,
            );

            rubi_star((&b__ * (&cos).pow(&p_)).pow(&m_) / (&b__ * &cos).pow(&m_ * &p_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3489_through_3492_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3489..=3492).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3489..=3492).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3493_through_3507_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3493..=3507).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3493..=3507).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (capital_a__
            + capital_b__ * i_sin(e__ + f__ * x_)
            + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (capital_a__ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let capital_a_ = symbols.capital_a_;
    let capital_c__ = symbols.capital_c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (capital_a_ + capital_c__ * i_sin(e__ + f__ * x_).pow(2))
}
