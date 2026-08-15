use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_35(rules);
    push_rules_rule_36(rules);
    push_rules_rule_37(rules);
    push_rules_rule_38(rules);
    push_rules_rule_39(rules);
    push_rules_rule_40(rules);
    push_rules_rule_41(rules);
    push_rules_rule_42(rules);
    push_rules_rule_43(rules);
    push_rules_rule_44(rules);
    push_rules_rule_45(rules);
    push_rules_rule_46(rules);
    push_rules_rule_47(rules);
    push_rules_rule_48(rules);
    push_rules_rule_49(rules);
    push_rules_rule_50(rules);
    push_rules_rule_51(rules);
    push_rules_rule_52(rules);
    push_rules_rule_53(rules);
    push_rules_rule_54(rules);
    push_rules_rule_55(rules);
    push_rules_rule_56(rules);
    push_rules_rule_57(rules);
    push_rules_rule_58(rules);
    push_rules_rule_59(rules);
    push_rules_rule_60(rules);
    push_rules_rule_61(rules);
    push_rules_rule_62(rules);
    push_rules_rule_63(rules);
    push_rules_rule_64(rules);
    push_rules_rule_65(rules);
    push_rules_rule_66(rules);
    push_rules_rule_67(rules);
    push_rules_rule_68(rules);
    push_rules_rule_69(rules);
    push_rules_rule_70(rules);
    push_rules_rule_71(rules);
    push_rules_rule_72(rules);
    push_rules_rule_73(rules);
    push_rules_rule_74(rules);
    push_rules_rule_75(rules);
    push_rules_rule_76(rules);
    push_rules_rule_77(rules);
    push_rules_rule_78(rules);
    push_rules_rule_79(rules);
    push_rules_rule_80(rules);
    push_rules_rule_81(rules);
}

fn push_rules_rule_35(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 35,
        source: "Int[u_.*(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.,x_Symbol] :=
          (b/d)^m \\[Star] Int[u*(c+d*x)^(m+n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0] && IntegerQ[m] && Not[IntegerQ[n] && SimplerQ[a+b*x,c+d*x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, a__, b__, c__, d__, m_, n_, x_],
        optional: [u__, b__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        proportional: [(a__, b__, c__, d__)],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && !(integerq!(n_) && simplerq!(&a__ + &b__ * x_, &c__ + &d__ * x_))
        },
        rhs: {
            let multiplier = (&b__ / &d__).pow(&m_);
            let integrand = u__ * (&c__ + &d__ * x_).pow(&m_ + &n_);
            rubi_star(multiplier, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_36(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 36,
        source: "Int[u_.*(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (b/d)^m \\[Star] Int[u*(c+d*x)^(m+n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0] && GtQ[b/d,0] && Not[SimplerQ[a+b*x,c+d*x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, a__, b__, c__, d__, m_, n_, x_],
        optional: [u__, b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        proportional: [(a__, b__, c__, d__)],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(&b__ / &d__, 0)
                && !simplerq!(&a__ + &b__ * x_, &c__ + &d__ * x_)
        },
        rhs: {
            let multiplier = (&b__ / &d__).pow(&m_);
            let integrand = u__ * (&c__ + &d__ * x_).pow(&m_ + &n_);
            rubi_star(multiplier, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_37(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 37,
        source: "Int[u_.*(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^m/(c+d*x)^m \\[Star] Int[u*(c+d*x)^(m+n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0] && Not[SimplerQ[a+b*x,c+d*x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, a__, b__, c__, d__, m_, n_, x_],
        optional: [u__, b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        proportional: [(a__, b__, c__, d__)],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && !simplerq!(&a__ + &b__ * x_, &c__ + &d__ * x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let multiplier = first.pow(&m_) / second.pow(&m_);
            let integrand = u__ * second.pow(&m_ + &n_);
            rubi_star(multiplier, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_38(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 38,
        source: "Int[(a_+b_.*x_)^m_.*(c_+d_.*x_),x_Symbol] :=
          d*x*(a+b*x)^(m+1)/(b*(m+2)) /;
        FreeQ[{a,b,c,d,m},x] && EqQ[a*d-b*c*(m+2),0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(&a__ * &d__ - &b__ * &c__ * (&m_ + Atom::num(2)), 0)
        },
        rhs: {
            rubi_simp(&(&d__ * x_ * (&a__ + &b__ * x_).pow(&m_ + Atom::num(1))
                    / (&b__ * (&m_ + Atom::num(2)))), x_)
        },
    ));
}

fn push_rules_rule_47(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 47,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*x),x] - d/(b*c-a*d) \\[Star] Int[1/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_) * (c__ + d__ * x_)),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let lhs = a__ + &b__ * x_;
            let rhs = c__ + &d__ * x_;
            let left = rubi_rhs_int(&(Atom::num(1) / lhs), x_);
            let right = rubi_rhs_int(&(Atom::num(1) / rhs), x_);
            rubi_star(&b__ / &det, left)
                    - rubi_star(&d__ / det, right)
        },
    ));
}

fn push_rules_rule_48(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 48,
        source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[m+n+2,0] && NeQ[m,-1]",
        desc: "Linear recurrence 3 with m+n+2\\[Equal]0",
        refs: ["G&R 2.155, CRC 59a with m+n+2\\[Equal]0", "G&R 2.110.2 or 2.110.6 with k=1 and m+n+2\\[Equal]0"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&m_ + &n_ + Atom::num(2), 0)
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let m1 = m_ + Atom::num(1);
            // The Rubi source returns this expression directly.  In
            // particular, Mathematica keeps positive integer powers of the
            // affine factors intact here.  Running Simp eagerly expands those
            // powers, which prevents callers such as inverse-sine rule 5254
            // from reaching the algebraic recurrence at DownValue 715.
            (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(n_ + Atom::num(1))
                / ((b__ * c__ - a__ * d__) * m1)
        },
    ));
}

fn push_rules_rule_49(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 49,
        source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[m+n+2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        // Both exponent predicates are integer predicates, so they also imply
        // that m and n are free of the integration variable.
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(m_, 0)
                && igtq!(&m_ + &n_ + Atom::num(2), 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_).pow(m_)
                * (&c__ + &d__ * x_).pow(n_);
            rubi_rhs_int(&rubi_expand_integrand(&integrand, x_), x_)
        },
    ));
}

fn push_rules_rule_50(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 50,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (a*c+b*d*x^2)^m/(2*d*m) + a \\[Star] Int[(a*c+b*d*x^2)^n,x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c+a*d,0] && EqQ[m-n,1] && GtQ[m,0] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(&m_ - &n_, 1)
                && gtq!(m_, 0)
                && (integerq!(m_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let direct = quadratic.pow(&m_) / (Atom::num(2) * &d__ * &m_);
            let recursive = rubi_rhs_int(&quadratic.pow(n_), x_);
            rubi_simp(&(direct), x_) + rubi_star(a__, recursive)
        },
    ));
}

fn push_rules_rule_40(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 40,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
          x*(a+b*x)^m*(c+d*x)^m/(2*m+1) + 2*a*c*m/(2*m+1) \\[Star] Int[(a+b*x)^(m-1)*(c+d*x)^(m-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && IGtQ[m+1/2,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let den = Atom::num(2) * &m_ + Atom::num(1);
            let direct = x_
                * (&a__ + &b__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&m_)
                / &den;
            let coefficient = Atom::num(2) * &a__ * &c__ * &m_ / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(&m_ - Atom::num(1))
                    * (c__ + d__ * x_).pow(&m_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_41(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 41,
        source: "Int[1/((a_+b_.*x_)^(3/2)*(c_+d_.*x_)^(3/2)),x_Symbol] :=
          x/(a*c*Sqrt[a+b*x]*Sqrt[c+d*x]) /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_).pow((3, 2)) * (c__ + d__ * x_).pow((3, 2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
        },
        rhs: {
            rubi_simp(&(x_
                    / (&a__
                    * &c__
                    * (a__ + b__ * x_).sqrt()
                    * (c__ + d__ * x_).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_42(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 42,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
          -x*(a+b*x)^(m+1)*(c+d*x)^(m+1)/(2*a*c*(m+1)) +
          (2*m+3)/(2*a*c*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(m+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && ILtQ[m+3/2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && iltq!(&m_ + Atom::num(3) / Atom::num(2), 0)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let den = Atom::num(2) * &a__ * &c__ * &m1;
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let direct = Atom::num(-1) * x_ * lhs.pow(&m1) * rhs.pow(&m1) / &den;
            let coefficient = (Atom::num(2) * m_ + Atom::num(3)) / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(&m1) * (c__ + d__ * x_).pow(m1)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_39(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 39,
        source: "Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^m_.,x_Symbol] :=
          Int[(a*c+b*d*x^2)^m,x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b*c+a*d,0] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && (integerq!(m_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            rubi_rhs_int(&((a__ * c__ + b__ * d__ * x_.pow(2)).pow(m_)), x_)
        },
    ));
}

fn push_rules_rule_46(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 46,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
          (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m] \\[Star] Int[(a*c+b*d*x^2)^m,x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b*c+a*d,0] && Not[IntegerQ[2*m]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && !integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let frac = rubi_frac_part(&m_);
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let primitive = rubi_rhs_int(&quadratic.pow(m_), x_);
            let multiplier =
                (a__ + b__ * x_).pow(&frac) * (c__ + d__ * x_).pow(&frac)
                    / quadratic.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_51(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 51,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+1)) -
          d*n/(b*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1),x] /;
        FreeQ[{a,b,c,d,n},x] && ILtQ[m,-1] && FractionQ[n] && GtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && iltq!(m_, -1)
                && fractionq!(n_)
                && gtq!(n_, 0)
        },
        rhs: {
            let m1 = m_ + Atom::num(1);
            let den = &b__ * &m1;
            let direct = (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(&n_)
                / &den;
            let coefficient = &d__ * &n_ / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(&m1)
                    * (c__ + d__ * x_).pow(&n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_52(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 52,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) -
          d*(m+n+2)/((b*c-a*d)*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
        FreeQ[{a,b,c,d,n},x] && ILtQ[m,-1] && FractionQ[n] && LtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && iltq!(m_, -1)
                && fractionq!(n_)
                && ltq!(n_, 0)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let det = &b__ * &c__ - &a__ * &d__;
            let den = det * &m1;
            let direct = (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(&n_ + Atom::num(1))
                / &den;
            let coefficient = &d__ * (&m_ + &n_ + Atom::num(2)) / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(m1) * (c__ + d__ * x_).pow(n_)),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_53(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 53,
        source: "Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] &&
          (Not[IntegerQ[n]] || EqQ[c,0] && LeQ[7*m+4*n+4,0] || LtQ[9*m+5*(n+1),0] || GtQ[m+n+2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 0)
                && (!integerq!(n_)
                    || eqq!(c__, Atom::num(0))
                        && leq!(
                            Atom::num(7) * &m_ + Atom::num(4) * &n_ + Atom::num(4),
                            0
                        )
                    || ltq!(Atom::num(9) * &m_ + Atom::num(5) * (&n_ + Atom::num(1)), 0)
                    || gtq!(&m_ + &n_ + Atom::num(2), 0))
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_54(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 54,
        source: "Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,0] && IntegerQ[n] && Not[IGtQ[n,0] && LtQ[m+n+2,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, c__, d__, n_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(m_, 0)
                && integerq!(n_)
                && !(igtq!(n_, 0) && ltq!(&m_ + &n_ + Atom::num(2), 0))
        },
        rhs: {
            let integrand = (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_55(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 55,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) -
          d*Simplify[m+n+2]/((b*c-a*d)*(m+1)) \\[Star] Int[(a+b*x)^Simplify[m+1]*(c+d*x)^n,x] /;
        FreeQ[{a,b,c,d,m,n},x] && ILtQ[Simplify[m+n+2],0] && NeQ[m,-1] &&
          Not[LtQ[m,-1] && LtQ[n,-1] && (EqQ[a,0] || NeQ[c,0] && LtQ[m-n,0] && IntegerQ[n])] &&
          (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && iltq!(rubi_simplify(&(&m_ + &n_ + Atom::num(2))), 0)
                && neq!(m_, -Atom::num(1))
                && !(ltq!(m_, -1)
                    && ltq!(n_, -1)
                    && (eqq!(a__, Atom::num(0))
                        || neq!(c__, Atom::num(0))
                            && ltq!(&m_ - &n_, 0)
                            && integerq!(n_)))
                && (sum_simplerq!(m_, 1) || !sum_simplerq!(n_, 1))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + Atom::num(1);
            let simplified_m1 = rubi_simplify(&m1);
            let m_n_2 = rubi_simplify(&(m_ + &n_ + Atom::num(2)));
            let den = det * &m1;
            let direct = (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(&n_ + Atom::num(1))
                / &den;
            let coefficient = &d__ * m_n_2 / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(simplified_m1) * (c__ + d__ * x_).pow(n_)),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_56(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 56,
        source: "Int[1/((a_+b_.*x_)^(9/4)*(c_+d_.*x_)^(1/4)),x_Symbol] :=
          -4/(5*b*(a+b*x)^(5/4)*(c+d*x)^(1/4)) - d/(5*b) \\[Star] Int[1/((a+b*x)^(5/4)*(c+d*x)^(5/4)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && NegQ[a^2*b^2]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.3 or 2.110.4 with k=1"],
        pattern: Atom::num(1) / ((a__ + b__ * x_).pow((9, 4)) * (c__ + d__ * x_).pow((1, 4))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && negq!(a__.pow(2) * b__.pow(2))
        },
        rhs: {
            let direct = -Atom::num(4)
                / (Atom::num(5)
                    * &b__
                    * (&a__ + &b__ * x_).pow((5, 4))
                    * (&c__ + &d__ * x_).pow((1, 4)));
            let coefficient = &d__ / (Atom::num(5) * &b__);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((a__ + &b__ * x_).pow((5, 4))
                        * (c__ + d__ * x_).pow((5, 4)))),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_57(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 57,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+1)) -
          d*n/(b*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[n,0] && LtQ[m,-1] && Not[IntegerQ[n] && Not[IntegerQ[m]]] &&
          Not[ILeQ[m+n+2,0] && (FractionQ[m] || GeQ[2*n+m+1,0])] && IntLinearQ[a,b,c,d,m,n,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
                && !(integerq!(n_) && !integerq!(m_))
                && !(ileq!(&m_ + &n_ + Atom::num(2), 0)
                    && (fractionq!(m_) || geq!(Atom::num(2) * &n_ + &m_ + Atom::num(1), 0)))
                && int_linearq!(a__, b__, c__, d__, m_, n_, x_)
        },
        rhs: {
            let m1 = m_ + Atom::num(1);
            let den = &b__ * &m1;
            let direct = (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(&n_)
                / &den;
            let coefficient = &d__ * &n_ / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(m1) * (c__ + d__ * x_).pow(n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_58(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 58,
        source: "Int[1/((a_+b_.*x_)^(5/4)*(c_+d_.*x_)^(1/4)),x_Symbol] :=
          -2/(b*(a+b*x)^(1/4)*(c+d*x)^(1/4)) + c \\[Star] Int[1/((a+b*x)^(5/4)*(c+d*x)^(5/4)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && NegQ[a^2*b^2]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.151, CRC 59b", "G&R 2.110.1 or 2.110.5 with k=1"],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_).pow((5, 4)) * (c__ + d__ * x_).pow((1, 4))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && negq!(a__.pow(2) * b__.pow(2))
        },
        rhs: {
            let direct = -Atom::num(2)
                / (&b__
                    * (&a__ + &b__ * x_).pow((1, 4))
                    * (&c__ + &d__ * x_).pow((1, 4)));
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((a__ + b__ * x_).pow((5, 4)) * (&c__ + d__ * x_).pow((5, 4)))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_59(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 59,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) +
          2*c*n/(m+n+1) \\[Star] Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && IGtQ[m+1/2,0] && IGtQ[n+1/2,0] && LtQ[m,n]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.151, CRC 59b", "G&R 2.110.1 or 2.110.5 with k=1"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
                && igtq!(&n_ + Atom::num(1) / Atom::num(2), 0)
                && ltq!(m_, n_)
        },
        rhs: {
            let den = &m_ + &n_ + Atom::num(1);
            let direct = (&a__ + &b__ * x_).pow(&m_ + Atom::num(1))
                * (&c__ + &d__ * x_).pow(&n_)
                / (&b__ * &den);
            let coefficient = Atom::num(2) * &c__ * &n_ / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_60(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 60,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) +
          n*(b*c-a*d)/(b*(m+n+1)) \\[Star] Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[n,0] && NeQ[m+n+1,0] &&
          Not[IGtQ[m,0] && (Not[IntegerQ[n]] || GtQ[m,0] && LtQ[m-n,0])] &&
          Not[ILtQ[m+n+2,0]] && IntLinearQ[a,b,c,d,m,n,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(n_, 0)
                && neq!(&m_ + &n_ + Atom::num(1), Atom::num(0))
                && !(igtq!(m_, 0)
                    && (!integerq!(n_) || gtq!(m_, 0) && ltq!(&m_ - &n_, 0)))
                && !iltq!(&m_ + &n_ + Atom::num(2), 0)
                && int_linearq!(a__, b__, c__, d__, m_, n_, x_)
        },
        rhs: {
            let den = &b__ * (&m_ + &n_ + Atom::num(1));
            let direct = (&a__ + &b__ * x_).pow(&m_ + Atom::num(1))
                * (&c__ + &d__ * x_).pow(&n_)
                / &den;
            let coefficient = &n_ * (&b__ * &c__ - &a__ * &d__) / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_61(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 61,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) -
          d*(m+n+2)/((b*c-a*d)*(m+1)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
        FreeQ[{a,b,c,d,n},x] && LtQ[m,-1] &&
          Not[LtQ[n,-1] && (EqQ[a,0] || NeQ[c,0] && LtQ[m-n,0] && IntegerQ[n])] && IntLinearQ[a,b,c,d,m,n,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && ltq!(m_, -1)
                && !(ltq!(n_, -1)
                    && (eqq!(a__, Atom::num(0))
                        || neq!(c__, Atom::num(0))
                            && ltq!(&m_ - &n_, 0)
                            && integerq!(n_)))
                && int_linearq!(a__, b__, c__, d__, m_, n_, x_)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + Atom::num(1);
            let den = det * &m1;
            let direct = (&a__ + &b__ * x_).pow(&m1)
                * (&c__ + &d__ * x_).pow(&n_ + Atom::num(1))
                / &den;
            let coefficient = &d__ * (&m_ + &n_ + Atom::num(2)) / den;
            let recursive = rubi_rhs_int(
                &((a__ + b__ * x_).pow(m1) * (c__ + d__ * x_).pow(n_)),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_43(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 43,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          ArcCosh[b*x/a]/(b*Sqrt[d/b]) /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && GtQ[a,0] && GtQ[d/b,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(a__, 0)
                && gtq!(&d__ / &b__, 0)
        },
        rhs: {
            rubi_simp(&((&b__ * x_ / &a__).acosh() / (&b__ * (&d__ / &b__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_44(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 44,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          2/(b*Sqrt[c]) \\[Star] Subst[Int[1/Sqrt[2-x^2/a],x],x,Sqrt[a+b*x]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && GtQ[c,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(2) - sub.pow(2) / &a__).sqrt()),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&a__ + &b__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) / (&b__ * c__.sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_45(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 45,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          2 \\[Star] Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && Not[GtQ[c,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && !gtq!(c__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&b__ - &d__ * sub.pow(2))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&a__ + &b__ * x_).sqrt() / (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_62(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 62,
        source: "Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          Int[1/Sqrt[a*c-b*(a-c)*x-b^2*x^2],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b+d,0] && GtQ[a+c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ + &d__, Atom::num(0))
                && gtq!(&a__ + &c__, 0)
        },
        rhs: {
            rubi_rhs_int(
                &(Atom::num(1)
                    / (&a__ * &c__
                        - &b__ * (a__ - c__) * x_
                        - b__.pow(2) * x_.pow(2))
                    .sqrt()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_63(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 63,
        source: "Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          2/b \\[Star] Subst[Int[1/Sqrt[c+d*x^2/b],x],x,Sqrt[b*x]] /;
        FreeQ[{b,c,d},x] && GtQ[c,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__],
        when: { freeq!([b__, c__, d__], x_) && gtq!(c__, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&c__ + &d__ * sub.pow(2) / &b__).sqrt()),
                sub_symbol,
            );
            let substituted =
                substitute_symbol(&primitive, sub_symbol, (&b__ * x_).sqrt());
            rubi_star(Atom::num(2) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_64(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 64,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
          2/b \\[Star] Subst[Int[1/Sqrt[c-a*d/b+d*x^2/b],x],x,Sqrt[a+b*x]] /;
        FreeQ[{a,b,c,d},x] && GtQ[c-a*d/b,0] && (Not[GtQ[a-c*b/d,0]] || PosQ[b])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(&c__ - &a__ * &d__ / &b__, 0)
                && (!gtq!(&a__ - &c__ * &b__ / &d__, 0) || posq!(b__))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&c__ - &a__ * &d__ / &b__ + &d__ * sub.pow(2) / &b__).sqrt()),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&a__ + &b__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_65(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 65,
        source: "Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          2 \\[Star] Subst[Int[1/(b-d*x^2),x],x,Sqrt[b*x]/Sqrt[c+d*x]] /;
        FreeQ[{b,c,d},x] && Not[GtQ[c,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__],
        when: { freeq!([b__, c__, d__], x_) && !gtq!(c__, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&b__ - &d__ * sub.pow(2))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&b__ * x_).sqrt() / (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_66(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 66,
        source: "Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
          2 \\[Star] Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && Not[GtQ[c-a*d/b,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && !gtq!(&c__ - &a__ * &d__ / &b__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&b__ - &d__ * sub.pow(2))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                (&a__ + &b__ * x_).sqrt() / (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_67(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 67,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
          With[{q=Rt[(b*c-a*d)/b,3]},
          -Log[RemoveContent[a+b*x,x]]/(2*b*q) -
          3/(2*b*q) \\[Star] Subst[Int[1/(q-x),x],x,(c+d*x)^(1/3)] +
          3/(2*b) \\[Star] Subst[Int[1/(q^2+q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!((&b__ * &c__ - &a__ * &d__) / &b__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let q = rubi_rt(&((&b__ * &c__ - &a__ * &d__) / &b__), 3);
            let substitution = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            let first = rubi_rhs_int(&(Atom::num(1) / (&q - &sub)), sub_symbol);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (q.pow(2) + &q * &sub + sub.pow(2))),
                sub_symbol,
            );
            let direct = -rubi_remove_content(&(&a__ + &b__ * x_), x_).log()
                / (Atom::num(2) * &b__ * &q);
            let first = substitute_symbol(&first, sub_symbol, &substitution);
            let second = substitute_symbol(&second, sub_symbol, substitution);
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * &q), first)
                    + rubi_star(Atom::num(3) / (Atom::num(2) * b__), second)
        },
    ));
}

fn push_rules_rule_68(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 68,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
          With[{q=Rt[-(b*c-a*d)/b,3]},
          Log[RemoveContent[a+b*x,x]]/(2*b*q) -
          3/(2*b*q) \\[Star] Subst[Int[1/(q+x),x],x,(c+d*x)^(1/3)] +
          3/(2*b) \\[Star] Subst[Int[1/(q^2-q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!((&b__ * &c__ - &a__ * &d__) / &b__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let q = rubi_rt(&(-((&b__ * &c__ - &a__ * &d__) / &b__)), 3);
            let substitution = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            let first = rubi_rhs_int(&(Atom::num(1) / (&q + &sub)), sub_symbol);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (q.pow(2) - &q * &sub + sub.pow(2))),
                sub_symbol,
            );
            let direct = rubi_remove_content(&(&a__ + &b__ * x_), x_).log()
                / (Atom::num(2) * &b__ * &q);
            let first = substitute_symbol(&first, sub_symbol, &substitution);
            let second = substitute_symbol(&second, sub_symbol, substitution);
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * &q), first)
                    + rubi_star(Atom::num(3) / (Atom::num(2) * b__), second)
        },
    ));
}

fn push_rules_rule_69(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 69,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
          With[{q=Rt[(b*c-a*d)/b,3]},
          -Log[RemoveContent[a+b*x,x]]/(2*b*q^2) -
          3/(2*b*q^2) \\[Star] Subst[Int[1/(q-x),x],x,(c+d*x)^(1/3)] -
          3/(2*b*q) \\[Star] Subst[Int[1/(q^2+q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!((&b__ * &c__ - &a__ * &d__) / &b__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let q = rubi_rt(&((&b__ * &c__ - &a__ * &d__) / &b__), 3);
            let q2 = q.pow(2);
            let substitution = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            let first = rubi_rhs_int(&(Atom::num(1) / (&q - &sub)), sub_symbol);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (&q2 + &q * &sub + sub.pow(2))),
                sub_symbol,
            );
            let direct = -rubi_remove_content(&(&a__ + &b__ * x_), x_).log()
                / (Atom::num(2) * &b__ * &q2);
            let first = substitute_symbol(&first, sub_symbol, &substitution);
            let second = substitute_symbol(&second, sub_symbol, substitution);
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * &q2), first)
                    - rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * q), second)
        },
    ));
}

fn push_rules_rule_70(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 70,
        source: "Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
          With[{q=Rt[-(b*c-a*d)/b,3]},
          -Log[RemoveContent[a+b*x,x]]/(2*b*q^2) +
          3/(2*b*q^2) \\[Star] Subst[Int[1/(q+x),x],x,(c+d*x)^(1/3)] +
          3/(2*b*q) \\[Star] Subst[Int[1/(q^2-q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!((&b__ * &c__ - &a__ * &d__) / &b__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let q = rubi_rt(&(-((&b__ * &c__ - &a__ * &d__) / &b__)), 3);
            let q2 = q.pow(2);
            let substitution = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            let first = rubi_rhs_int(&(Atom::num(1) / (&q + &sub)), sub_symbol);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (&q2 - &q * &sub + sub.pow(2))),
                sub_symbol,
            );
            let direct = -rubi_remove_content(&(&a__ + &b__ * x_), x_).log()
                / (Atom::num(2) * &b__ * &q2);
            let first = substitute_symbol(&first, sub_symbol, &substitution);
            let second = substitute_symbol(&second, sub_symbol, substitution);
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * &q2), first)
                    + rubi_star(Atom::num(3) / (Atom::num(2) * &b__ * q), second)
        },
    ));
}

fn push_rules_rule_71(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 71,
        source: "Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
          With[{q=Rt[d/b,3]},
          -Sqrt[3]*q/d*ArcTan[2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))+1/Sqrt[3]] -
          q/(2*d)*Log[c+d*x] -
          3*q/(2*d)*Log[q*(a+b*x)^(1/3)/(c+d*x)^(1/3)-1]] /;
        FreeQ[{a,b,c,d},x] && PosQ[d/b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && posq!(&d__ / &b__)
        },
        rhs: {
            let q = rubi_rt(&(&d__ / &b__), 3);
            let sqrt3 = Atom::num(3).sqrt();
            let lhs = (&a__ + &b__ * x_).pow(Atom::num(1) / Atom::num(3));
            let rhs = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            rubi_simp(&(-&sqrt3 * &q
                    * (Atom::num(2) * &q * &lhs / (&sqrt3 * &rhs)
                        + Atom::num(1) / &sqrt3)
                        .atan()
                    / &d__), x_)
                    - rubi_simp(&(&q * (&c__ + &d__ * x_).log() / (Atom::num(2) * &d__)), x_)
                    - rubi_simp(&(Atom::num(3) * &q * (&q * lhs / rhs - Atom::num(1)).log()
                        / (Atom::num(2) * d__)), x_)
        },
    ));
}

fn push_rules_rule_72(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 72,
        source: "Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
          With[{q=Rt[-d/b,3]},
          Sqrt[3]*q/d*ArcTan[1/Sqrt[3]-2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))] +
          q/(2*d)*Log[c+d*x] +
          3*q/(2*d)*Log[q*(a+b*x)^(1/3)/(c+d*x)^(1/3)+1]] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &b__)
        },
        rhs: {
            let q = rubi_rt(&(-&d__ / &b__), 3);
            let sqrt3 = Atom::num(3).sqrt();
            let lhs = (&a__ + &b__ * x_).pow(Atom::num(1) / Atom::num(3));
            let rhs = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(3));
            rubi_simp(&(&sqrt3 * &q
                    * (Atom::num(1) / &sqrt3
                        - Atom::num(2) * &q * &lhs / (&sqrt3 * &rhs))
                        .atan()
                    / &d__), x_)
                    + rubi_simp(&(&q * (&c__ + &d__ * x_).log() / (Atom::num(2) * &d__)), x_)
                    + rubi_simp(&(Atom::num(3) * &q * (&q * lhs / rhs + Atom::num(1)).log()
                        / (Atom::num(2) * d__)), x_)
        },
    ));
}

fn push_rules_rule_73(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 73,
        source: "Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          With[{p=Denominator[m]},
          p/b \\[Star] Subst[Int[x^(p*(m+1)-1)*(c-a*d/b+d*x^p/b)^n,x],x,(a+b*x)^(1/p)]] /;
        FreeQ[{a,b,c,d},x] && LtQ[-1,m,0] && LeQ[-1,n,0] && LeQ[Denominator[n],Denominator[m]] &&
          IntLinearQ[a,b,c,d,m,n,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && ltq!(-1, m_, 0)
                && leq!(Atom::num(-1), n_, Atom::num(0))
                && leq!(
                    Atom::num(denominator!(n_)),
                    Atom::num(denominator!(m_))
                )
                && int_linearq!(a__, b__, c__, d__, m_, n_, x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let p = Atom::num(denominator!(m_));
            let transformed_exponent =
                (&p * (&m_ + Atom::num(1)) - Atom::num(1)).expand();
            let transformed_affine =
                c__ - &a__ * &d__ / &b__ + d__ * sub.pow(&p) / &b__;
            let primitive = rubi_rhs_int(
                &(sub.pow(transformed_exponent) * transformed_affine.pow(n_)),
                sub_symbol,
            );
            let substitution = (a__ + &b__ * x_).pow(Atom::num(1) / &p);
            let substituted = substitute_symbol(&primitive, sub_symbol, substitution);
            rubi_star(&p / &b__, substituted)
        },
    ));
}

fn push_rules_rule_74(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 74,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          c^n*(b*x)^(m+1)/(b*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*x/c] /;
        FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && (IntegerQ[n] || GtQ[c,0] && Not[EqQ[n,-1/2] && EqQ[c^2-d^2,0] && GtQ[-d/(b*c),0]])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__, m_, n_],
        when: {
            freeq!([b__, c__, d__, m_, n_], x_)
                && !integerq!(m_)
                && (integerq!(n_)
                    || gtq!(c__, 0)
                        && !(eqq!(n_, -Atom::num(1) / Atom::num(2))
                            && eqq!(&c__ * &c__ - &d__ * &d__, Atom::num(0))
                            && gtq!(-&d__ / (&b__ * &c__), 0)))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let m2 = &m_ + Atom::num(2);
            rubi_simp(&(c__.pow(&n_) * (&b__ * x_).pow(&m1) / (&b__ * &m1)
                    * rubi_hypergeometric2f1(-&n_, m1, m2, -&d__ * x_ / &c__)), x_)
        },
    ));
}

fn push_rules_rule_75(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 75,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m)*Hypergeometric2F1[-m,n+1,n+2,1+d*x/c] /;
        FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[n]] && (IntegerQ[m] || GtQ[-d/(b*c),0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__, m_, n_],
        when: {
            freeq!([b__, c__, d__, m_, n_], x_)
                && !integerq!(n_)
                && (integerq!(m_) || gtq!(-&d__ / (&b__ * &c__), 0))
        },
        rhs: {
            let n1 = &n_ + Atom::num(1);
            let n2 = &n_ + Atom::num(2);
            rubi_simp(&((&c__ + &d__ * x_).pow(&n1)
                    / (&d__ * &n1 * (-&d__ / (&b__ * &c__)).pow(&m_))
                    * rubi_hypergeometric2f1(
                        -&m_,
                        n1,
                        n2,
                        Atom::num(1) + &d__ * x_ / &c__,
                    )), x_)
        },
    ));
}

fn push_rules_rule_76(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 76,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n] \\[Star] Int[(b*x)^m*(1+d*x/c)^n,x] /;
        FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]] && Not[GtQ[-d/(b*c),0]] &&
          (RationalQ[m] && Not[EqQ[n,-1/2] && EqQ[c^2-d^2,0]] || Not[RationalQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__, m_, n_],
        when: {
            freeq!([b__, c__, d__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !gtq!(c__, 0)
                && !gtq!(-&d__ / (&b__ * &c__), 0)
                && (rationalq!(m_)
                    && !(eqq!(n_, -Atom::num(1) / Atom::num(2))
                        && eqq!(&c__ * &c__ - &d__ * &d__, Atom::num(0)))
                    || !rationalq!(n_))
        },
        rhs: {
            let int_n = rubi_int_part(&n_);
            let frac_n = rubi_frac_part(&n_);
            let normalized = Atom::num(1) + &d__ * x_ / &c__;
            let primitive = rubi_rhs_int(&((&b__ * x_).pow(m_) * normalized.pow(n_)), x_);
            let multiplier = c__.pow(int_n) * (&c__ + &d__ * x_).pow(&frac_n)
                / normalized.pow(frac_n);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_77(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 77,
        source: "Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (-b*c/d)^IntPart[m]*(b*x)^FracPart[m]/(-d*x/c)^FracPart[m] \\[Star] Int[(-d*x/c)^m*(c+d*x)^n,x] /;
        FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]] && Not[GtQ[-d/(b*c),0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [b__, c__, d__, m_, n_],
        when: {
            freeq!([b__, c__, d__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !gtq!(c__, 0)
                && !gtq!(-&d__ / (&b__ * &c__), 0)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let scaled = -&d__ * x_ / &c__;
            let primitive =
                rubi_rhs_int(&(scaled.pow(&m_) * (&c__ + &d__ * x_).pow(n_)), x_);
            let multiplier = (-&b__ * &c__ / &d__).pow(int_m)
                * (&b__ * x_).pow(&frac_m)
                / scaled.pow(frac_m);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_78(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 78,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (b*c-a*d)^n*(a+b*x)^(m+1)/(b^(n+1)*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*(a+b*x)/(b*c-a*d)] /;
        FreeQ[{a,b,c,d,m},x] && Not[IntegerQ[m]] && IntegerQ[n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && !integerq!(m_)
                && integerq!(n_)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + Atom::num(1);
            let m2 = &m_ + Atom::num(2);
            let n1 = &n_ + Atom::num(1);
            let affine = &a__ + &b__ * x_;
            rubi_simp(&(det.pow(&n_) * affine.pow(&m1)
                    / (b__.pow(&n1) * &m1)
                    * rubi_hypergeometric2f1(
                        -&n_,
                        m1,
                        m2,
                        -&d__ * affine / det,
                    )), x_)
        },
    ));
}

fn push_rules_rule_79(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 79,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^(m+1)/(b*(m+1)*(b/(b*c-a*d))^n)*Hypergeometric2F1[-n,m+1,m+2,-d*(a+b*x)/(b*c-a*d)] /;
        FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[b/(b*c-a*d),0] &&
          (RationalQ[m] || Not[RationalQ[n] && GtQ[-d/(b*c-a*d),0]])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(&b__ / (&b__ * &c__ - &a__ * &d__), 0)
                && (rationalq!(m_)
                    || !(rationalq!(n_)
                        && gtq!(-&d__ / (&b__ * &c__ - &a__ * &d__), 0)))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + Atom::num(1);
            let m2 = &m_ + Atom::num(2);
            let affine = &a__ + &b__ * x_;
            rubi_simp(&(affine.pow(&m1)
                    / (&b__ * &m1 * (&b__ / &det).pow(&n_))
                    * rubi_hypergeometric2f1(
                        -&n_,
                        m1,
                        m2,
                        -&d__ * affine / det,
                    )), x_)
        },
    ));
}

fn push_rules_rule_80(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 80,
        source: "Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
          (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n]) \\[Star]
            Int[(a+b*x)^m*Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && (RationalQ[m] || Not[SimplerQ[n+1,m+1]])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && (rationalq!(m_)
                    || !simplerq!(&n_ + Atom::num(1), &m_ + Atom::num(1)))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let int_n = rubi_int_part(&n_);
            let frac_n = rubi_frac_part(&n_);
            let cd = &c__ + &d__ * x_;
            let simp = simp!(&b__ * &c__ / &det + &b__ * &d__ * x_ / &det, x_);
            let primitive = rubi_rhs_int(&((&a__ + &b__ * x_).pow(m_) * simp.pow(n_)), x_);
            let multiplier = cd.pow(&frac_n)
                / ((&b__ / &det).pow(int_n) * (&b__ * cd / &det).pow(frac_n));
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_81(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__);
    let rule = rubi_rule!(
        order: 81,
        source: "Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,u] /;
        FreeQ[{a,b,c,d,m,n},x] && LinearQ[u,x] && NeQ[Coefficient[u,x,0],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__).pow(m_) * (c__ + d__ * u__).pow(n_),
        with: [a__, b__, c__, d__, u__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, m_, n_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_coefficient(&u__, x_, 0).is_some_and(|u0| neq!(u0, 0))
        },
        rhs: {
            let Some((_u0, u1)) = linear_coefficients(&u__, x_) else {
                panic!("Rubi RHS invariant was not established by the rule condition");
            };
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &((a__ + b__ * &sub).pow(m_) * (c__ + d__ * &sub).pow(n_)),
                sub_symbol,
            );
            let substituted = substitute_symbol(&primitive, sub_symbol, u__);
            rubi_star(Atom::num(1) / u1, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u__)
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
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_) * (c__ + d__ * x_).pow((1, 3)))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_) * (c__ + d__ * x_).pow((2, 3)))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_).pow((1, 3)) * (c__ + d__ * x_).pow((2, 3)))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_).sqrt() * (c__ + d__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((b__ * x_).sqrt() * (c__ + d__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
}
