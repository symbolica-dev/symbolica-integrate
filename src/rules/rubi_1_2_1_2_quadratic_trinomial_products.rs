use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1098(rules);
    push_rules_rule_1099(rules);
    push_rules_rule_1100(rules);
    push_rules_rule_1101(rules);
    push_rules_rule_1102(rules);
    push_rules_rule_1103(rules);
    push_rules_rule_1104(rules);
    push_rules_rule_1105(rules);
    push_rules_rule_1106(rules);
    push_rules_rule_1107(rules);
    push_rules_rule_1108(rules);
    push_rules_rule_1109(rules);
    push_rules_rule_1110(rules);
    push_rules_rule_1111(rules);
    push_rules_rule_1112(rules);
    push_rules_rule_1113(rules);
    push_rules_rule_1114(rules);
    push_rules_rule_1115(rules);
    push_rules_rule_1116(rules);
    push_rules_rule_1117(rules);
    push_rules_rule_1118(rules);
    push_rules_rule_1119(rules);
    push_rules_rule_1120(rules);
    push_rules_rule_1121(rules);
    push_rules_rule_1122(rules);
    push_rules_rule_1123(rules);
    push_rules_rule_1124(rules);
    push_rules_rule_1125(rules);
    push_rules_rule_1126(rules);
    push_rules_rule_1127(rules);
    push_rules_rule_1128(rules);
    push_rules_rule_1129(rules);
    push_rules_rule_1130(rules);
    push_rules_rule_1131(rules);
    push_rules_rule_1132(rules);
    push_rules_rule_1133(rules);
    push_rules_rule_1134(rules);
    push_rules_rule_1135(rules);
    push_rules_rule_1136(rules);
    push_rules_rule_1137(rules);
    push_rules_rule_1138(rules);
    push_rules_rule_1139(rules);
    push_rules_rule_1140(rules);
    push_rules_rule_1141(rules);
    push_rules_rule_1142(rules);
    push_rules_rule_1143(rules);
    push_rules_rule_1144(rules);
    push_rules_rule_1145(rules);
    push_rules_rule_1146(rules);
    push_rules_rule_1147(rules);
    push_rules_rule_1148(rules);
    push_rules_rule_1149(rules);
    push_rules_rule_1150(rules);
    push_rules_rule_1151(rules);
    push_rules_rule_1152(rules);
    push_rules_rule_1153(rules);
    push_rules_rule_1154(rules);
    push_rules_rule_1155(rules);
    push_rules_rule_1156(rules);
    push_rules_rule_1157(rules);
    push_rules_rule_1158(rules);
    push_rules_rule_1159(rules);
    push_rules_rule_1160(rules);
    push_rules_rule_1161(rules);
    push_rules_rule_1162(rules);
    push_rules_rule_1163(rules);
    push_rules_rule_1164(rules);
    push_rules_rule_1165(rules);
    push_rules_rule_1166(rules);
    push_rules_rule_1167(rules);
    push_rules_rule_1168(rules);
    push_rules_rule_1169(rules);
    push_rules_rule_1170(rules);
    push_rules_rule_1171(rules);
    push_rules_rule_1172(rules);
    push_rules_rule_1173(rules);
    push_rules_rule_1174(rules);
    push_rules_rule_1175(rules);
    push_rules_rule_1176(rules);
    push_rules_rule_1177(rules);
    push_rules_rule_1178(rules);
    push_rules_rule_1179(rules);
    push_rules_rule_1180(rules);
}

fn push_rules_rule_1098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1098,
        source: "Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          1/c^p \\[Star] Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, c__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_1099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1099,
        source: "Int[(d_+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e^m*(a+b*x+c*x^2)^(p+(m+1)/2)/(c^((m+1)/2)*(m+2*p+1)) /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && IntegerQ[(m-1)/2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, c__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let half_m_plus_one = (&m_ + Atom::num(1)) / Atom::num(2);
            rubi_simp(&(e__.pow(&m_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + &half_m_plus_one)
                    / (c__.pow(&half_m_plus_one) * (&m_ + Atom::num(2) * &p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_1100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1100,
        source: "Int[(d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + (2*c*d-b*e)/(2*c) \\[Star] Int[(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b^2-4*a*c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &e__ * quadratic.pow(&p_ + 1)
                / (Atom::num(2) * &c__ * (&p_ + 1));
            let coefficient = (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                / (Atom::num(2) * &c__);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, rubi_rhs_int(&quadratic.pow(&p_), x_))
        },
    ));
}

fn push_rules_rule_1101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1101,
        source: "Int[x_^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p])) \\[Star] Int[ExpandLinearProduct[(b/2+c*x)^(2*p),x^m,b/2,c,x],x] /;
        FreeQ[{a,b,c,m,p},x] && EqQ[b^2-4*a*c,0] && IGtQ[m,0] && EqQ[m-2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(m_, 0)
                && eqq!(&m_ - Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ / Atom::num(2) + &c__ * x_;
            let frac_p = rubi_frac_part(&p_);
            let expanded = rubi_expand_linear_product(
                &linear.pow(Atom::num(2) * &p_),
                x_.pow(&m_),
                &(&b__ / Atom::num(2)),
                &c__,
                x_,
            ).rubi_rhs();
            let coefficient = quadratic.pow(&frac_p)
                / (c__.pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * &frac_p));
            rubi_star(coefficient, rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1102,
        source: "Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p])) \\[Star] Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b^2-4*a*c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, c__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ / Atom::num(2) + &c__ * x_;
            let frac_p = rubi_frac_part(&p_);
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * linear.pow(Atom::num(2) * &p_);
            let coefficient = quadratic.pow(&frac_p)
                / (c__.pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * &frac_p));
            rubi_star(coefficient, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_1120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1120,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p] && (EqQ[m+p,0] || EqQ[m+2*p+2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(p_)
                && (eqq!(&m_ + &p_, 0)
                    || eqq!(&m_ + Atom::num(2) * &p_ + 2, 0))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_ + &p_)
                * (&a__ / &d__ + &c__ * x_ / &e__).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1121,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0] && LtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (integerq!(p_)
                    || gtq!(a__, 0) && gtq!(d__, 0) && ltq!(c__, 0))
        },
        rhs: {
            let payload = (&d__ + &e__ * x_).pow(&m_ + &p_)
                * (&a__ / &d__ + &c__ * x_ / &e__).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1103,
        source: "Int[(d_+e_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          d*Log[RemoveContent[a+b*x+c*x^2,x]]/b /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let content_removed = remove_integer_content(&(&a__ + &b__ * x_ + &c__ * x_.pow(2)), x_);
            rubi_simp(&(d__ * content_removed.log() / b__), x_)
        },
    ));
}

fn push_rules_rule_1104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1104,
        source: "Int[(d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          d*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[2*c*d-b*e,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            rubi_simp(&(d__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                    .pow(&p_ + Atom::num(1))
                    / (&b__ * (&p_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_1142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1142,
        source: "Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          (2*c*d-b*e)/(2*c) \\[Star] Int[1/(a+b*x+c*x^2),x] + e/(2*c) \\[Star] Int[(b+2*c*x)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a & G&R 2.161.3"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_coefficient = (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &c__);
            let second_coefficient = &e__ / (Atom::num(2) * &c__);
            let first_integrand = Atom::num(1) / &trinomial;
            let second_integrand = (&b__ + Atom::num(2) * &c__ * x_) / trinomial;
            rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1158,
        source: "Int[(d_.+e_.*x_)/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2*(b*d-2*a*e+(2*c*d-b*e)*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Quadratic recurrence 2a",
        refs: [],
        pattern: (d__ + e__ * x_) / (a__ + b__ * x_ + c__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            rubi_simp(&(-Atom::num(2)
                    * (&b__ * &d__ - Atom::num(2) * &a__ * &e__ + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                    / (discriminant * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_1159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1159,
        source: "Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (b*d-2*a*e+(2*c*d-b*e)*x)/((p+1)*(b^2-4*a*c))*(a+b*x+c*x^2)^(p+1) -
          (2*p+3)*(2*c*d-b*e)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(p_, -1)
                && neq!(p_, -(Atom::num(3) / Atom::num(2)))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = (&p_ + Atom::num(1)) * &discriminant;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = (&b__ * &d__
                - Atom::num(2) * &a__ * &e__
                + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = trinomial.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_) - rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                    * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                    / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1160,
        source: "Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + (2*c*d-b*e)/(2*c) \\[Star] Int[(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(p_, -1)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &c__ * (&p_ + Atom::num(1));
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &e__ * trinomial.pow(&p_ + Atom::num(1)) / direct_denominator;
            let recursive_integrand = trinomial.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                    / (Atom::num(2) * &c__), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1119,
        source: "Int[(e_.*x_)^m_.*(b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          1/e^p \\[Star] Int[(e*x)^(m+p)*(b+c*x)^p,x] /;
        FreeQ[{b,c,e,m},x] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, e__, m_, p_, x_],
        optional: [b__, c__, e__, m_, p_],
        when: { freeq!([b__, c__, e__, m_], x_) && integerq!(p_) },
        rhs: {
            let recursive_integrand =
                (&e__ * x_).pow((&m_ + &p_).expand()) * (&b__ + &c__ * x_).pow(&p_);
            rubi_star(Atom::num(1) / e__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1122,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
        },
        rhs: {
            rubi_simp(&(&e__ * (&d__ + &e__ * x_).pow(&m_ - Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / (&c__ * (&p_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_1123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1123,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)) /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
        },
        rhs: {
            rubi_simp(&(&e__ * (&d__ + &e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / ((&p_ + Atom::num(1))
                        * (Atom::num(2) * &c__ * &d__ - &b__ * &e__))), x_)
        },
    ));
}

fn push_rules_rule_1124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1124,
        source: "Int[(d_.+e_.*x_)^m_./(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2*e*(2*c*d-b*e)^(m-2)*(d+e*x)/(c^(m-1)*Sqrt[a+b*x+c*x^2]) +
          e^2/c^(m-1) \\[Star] Int[1/Sqrt[a+b*x+c*x^2]*ExpandToSum[((2*c*d-b*e)^(m-1)-c^(m-1)*(d+e*x)^(m-1))/(c*d-b*e-c*e*x),x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            / (a__ + b__ * x_ + c__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let proportional = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct = -Atom::num(2) * &e__ * proportional.pow(&m_ - 2) * &linear
                / (c__.pow(&m_ - 1) * quadratic.sqrt());
            let quotient = (proportional.pow(&m_ - 1)
                - c__.pow(&m_ - 1) * linear.pow(&m_ - 1))
                / (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_);
            let recursive_integrand = rubi_expand_to_sum(&quotient, x_) / quadratic.sqrt();
            let coefficient = e__.pow(2) / c__.pow(&m_ - 1);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1125,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -2*e^(2*m+3)*Sqrt[a+b*x+c*x^2]/((-2*c*d+b*e)^(m+2)*(d+e*x)) -
          e^(2*m+2) \\[Star] Int[1/Sqrt[a+b*x+c*x^2]*ExpandToSum[((-2*c*d+b*e)^(-m-1)-(-c*d+b*e+c*e*x)^(-m-1))/(d+e*x),x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[m,0] && EqQ[m+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && eqq!(&m_ + &p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let proportional = -Atom::num(2) * &c__ * &d__ + &b__ * &e__;
            let direct = -Atom::num(2) * e__.pow(Atom::num(2) * &m_ + 3)
                * quadratic.sqrt()
                / (proportional.pow(&m_ + 2) * &linear);
            let quotient = (proportional.pow(-&m_ - 1)
                - (-&c__ * &d__ + &b__ * &e__ + &c__ * &e__ * x_)
                    .pow(-&m_ - 1))
                / &linear;
            let recursive_integrand = rubi_expand_to_sum(&quotient, x_) / quadratic.sqrt();
            rubi_simp(&(direct), x_)
                    - rubi_star(e__.pow(Atom::num(2) * &m_ + 2), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1126,
        source: "Int[(d_.+e_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - e^2*(p+2)/(c*(p+1)) \\[Star] Int[(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1]",
        desc: "Special quadratic recurrence 2a",
        refs: [],
        pattern: (d__ + e__ * x_).pow(2) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &e__ * linear * trinomial.pow(&p_ + Atom::num(1))
                / (&c__ * (&p_ + Atom::num(1)));
            let coefficient = e__.pow(2) * (&p_ + Atom::num(2))
                / (&c__ * (&p_ + Atom::num(1)));
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&trinomial.pow(&p_ + Atom::num(1)), x_))
        },
    ));
}

fn push_rules_rule_1127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1127,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(a+b*x+c*x^2)^(m+p)/(a/d+c*x/e)^m,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[m] &&
          RationalQ[p] && (LtQ[0,-m,p] || LtQ[p,-m,0]) && NeQ[m,2] && NeQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(m_)
                && rationalq!(p_)
                && (ltq!(0, -&m_, &p_) || ltq!(&p_, -&m_, 0))
                && neq!(m_, 2)
                && neq!(m_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let transformed =
                trinomial.pow(&m_ + &p_) / (&a__ / &d__ + &c__ * x_ / &e__).pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_1128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1128,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) +
          Simplify[m+p]*(2*c*d-b*e)/(c*(m+2*p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[Simplify[m+p],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            let mp = (&m_ + &p_).expand();
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(mp, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1));
            let direct = &e__ * linear.pow(&m_ - Atom::num(1))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let coefficient = rubi_simplify(&(&m_ + &p_))
                * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                / denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1129,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) +
          c*Simplify[m+2*p+2]/((m+p+1)*(2*c*d-b*e)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[Simplify[m+2*p+2],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            let shifted = (&m_ + Atom::num(2) * &p_ + Atom::num(2)).expand();
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(shifted, 0)
        },
        rhs: {
            let shifted = (&m_ + Atom::num(2) * &p_ + Atom::num(2)).expand();
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator =
                (&m_ + &p_ + Atom::num(1)) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__);
            let direct = -&e__ * linear.pow(&m_) * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = linear.pow(&m_ + Atom::num(1)) * trinomial.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star(&c__ * shifted / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1136,
        source: "Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          2*e \\[Star] Subst[Int[1/(2*c*d-b*e+e^2*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let inner_integrand =
                Atom::num(1) / (Atom::num(2) * &c__ * &d__ - &b__ * &e__ + e__.pow(2) * sub_atom.pow(2));
            let primitive = rubi_rhs_int(&inner_integrand, sub_symbol);

            let substitution =
                (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt() / (&d__ + &e__ * x_).sqrt();

            rubi_star(Atom::num(2) * e__, rubi_subst(&primitive, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1130,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+p+1)) -
          c*p/(e^2*(m+p+1)) \\[Star] Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && (LtQ[m,-2] || EqQ[m+2*p+1,0]) && NeQ[m+p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
                && (ltq!(m_, -2) || eqq!(&m_ + Atom::num(2) * &p_ + 1, 0))
                && neq!(&m_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &e__ * (&m_ + &p_ + 1);
            let direct = linear.pow(&m_ + 1) * quadratic.pow(&p_) / denominator;
            let recursive_integrand = linear.pow(&m_ + 2) * quadratic.pow(&p_ - 1);
            rubi_simp(&(direct), x_) - rubi_star(&c__ * &p_ / (e__.pow(2) * (&m_ + &p_ + 1)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1131,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) -
          p*(2*c*d-b*e)/(e^2*(m+2*p+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && (LeQ[-2,m,0] || EqQ[m+p+1,0]) && NeQ[m+2*p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
                && (leq!(-2, m_, 0) || eqq!(&m_ + &p_ + 1, 0))
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &e__ * (&m_ + Atom::num(2) * &p_ + 1);
            let direct = linear.pow(&m_ + 1) * quadratic.pow(&p_) / denominator;
            let recursive_integrand = linear.pow(&m_ + 1) * quadratic.pow(&p_ - 1);
            rubi_simp(&(direct), x_) - rubi_star(&p_ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                    / (e__.pow(2) * (&m_ + Atom::num(2) * &p_ + 1)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1132,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) -
          (2*c*d-b*e)*(m+2*p+2)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && LtQ[0,m,1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && ltq!(0, m_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let factor = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct = &factor * linear.pow(&m_) * quadratic.pow(&p_ + 1)
                / (&e__ * (&p_ + 1) * &discriminant);
            let recursive_integrand = linear.pow(&m_ - 1) * quadratic.pow(&p_ + 1);
            rubi_simp(&(direct), x_) - rubi_star(&factor * (&m_ + Atom::num(2) * &p_ + 2)
                    / ((&p_ + 1) * discriminant), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1133,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) -
          e^2*(m+p)/(c*(p+1)) \\[Star] Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &c__ * (&p_ + 1);
            let direct = &e__ * linear.pow(&m_ - 1) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive_integrand = linear.pow(&m_ - 2) * quadratic.pow(&p_ + 1);
            rubi_simp(&(direct), x_) - rubi_star(e__.pow(2) * (&m_ + &p_) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1134,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) +
          (m+p)*(2*c*d-b*e)/(c*(m+2*p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &c__ * (&m_ + Atom::num(2) * &p_ + 1);
            let direct = &e__ * linear.pow(&m_ - 1) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive_integrand = linear.pow(&m_ - 1) * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star((&m_ + &p_) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                    / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1135,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) +
          c*(m+2*p+2)/((m+p+1)*(2*c*d-b*e)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[m,0] && NeQ[m+p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(m_, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let factor = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = (&m_ + &p_ + 1) * &factor;
            let direct = -&e__ * linear.pow(&m_) * quadratic.pow(&p_ + 1) / &denominator;
            let recursive_integrand = linear.pow(&m_ + 1) * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star(&c__ * (&m_ + Atom::num(2) * &p_ + 2) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1137,
        source: "Int[(e_.*x_)^m_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p) \\[Star] Int[x^(m+p)*(b+c*x)^p,x] /;
        FreeQ[{b,c,e,m},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [b__, c__, e__, m_, p_, x_],
        optional: [b__, c__, e__],
        when: { freeq!([b__, c__, e__, m_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let quadratic = &b__ * x_ + &c__ * x_.pow(2);
            let affine = &b__ + &c__ * x_;
            let denominator = x_.pow(&m_ + &p_) * affine.pow(&p_);
            let recursive_integrand = x_.pow(&m_ + &p_) * affine.pow(&p_);
            rubi_star(scaled.pow(&m_) * quadratic.pow(&p_) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1138,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          d^m*(a+b*x+c*x^2)^FracPart[p]/((1+e*x/d)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p]) \\[Star] Int[(1+e*x/d)^(m+p)*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && (IntegerQ[m] || GtQ[d,0]) &&
          Not[IGtQ[m,0] && (IntegerQ[3*p] || IntegerQ[4*p])]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (integerq!(m_) || gtq!(d__, 0))
                && !(igtq!(m_, 0)
                    && (integerq!(Atom::num(3) * &p_)
                        || integerq!(Atom::num(4) * &p_)))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let normalized_linear = Atom::num(1) + &e__ * x_ / &d__;
            let transformed_affine = &a__ / &d__ + &c__ * x_ / &e__;
            let coefficient = d__.pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&frac_p)
                / (normalized_linear.pow(&frac_p) * transformed_affine.pow(&frac_p));
            let recursive_integrand = normalized_linear.pow(&m_ + &p_)
                * transformed_affine.pow(&p_);
            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1139,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          d^IntPart[m]*(d+e*x)^FracPart[m]/(1+e*x/d)^FracPart[m] \\[Star] Int[(1+e*x/d)^m*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[m] || GtQ[d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !(integerq!(m_) || gtq!(d__, 0))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let normalized_linear = Atom::num(1) + &e__ * x_ / &d__;
            let denominator = normalized_linear.pow(&frac_m);
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let transformed_integrand = normalized_linear.pow(&m_) * quadratic.pow(&p_);
            let branch_factor = d__.pow(rubi_int_part(&m_)) * (&d__ + &e__ * x_).pow(&frac_m)
                / denominator;

            rubi_star(branch_factor, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1105,
        source: "Int[1/((d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
          -4*b*c/(d*(b^2-4*a*c)) \\[Star] Int[1/(b+2*c*x),x] +
          b^2/(d^2*(b^2-4*a*c)) \\[Star] Int[(d+e*x)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(-1) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(-1),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&b__ + Atom::num(2) * &c__ * x_)),
                x_,
            );
            let second = rubi_rhs_int(
                &((&d__ + &e__ * x_)
                    / (&a__ + &b__ * x_ + &c__ * x_.pow(2))),
                x_,
            );
            rubi_star(-Atom::num(4) * &b__ * &c__ / (&d__ * &discriminant), first) + rubi_star(b__.pow(2) / (d__.pow(2) * discriminant), second)
        },
    ));
}

fn push_rules_rule_1106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1106,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[2*c*d-b*e,0] && EqQ[m+2*p+3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            rubi_simp(&(Atom::num(2)
                    * &c__
                    * (&d__ + &e__ * x_).pow(&m_ + 1)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + 1)
                    / (&e__ * (&p_ + 1) * discriminant)), x_)
        },
    ));
}

fn push_rules_rule_1107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1107,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[2*c*d-b*e,0] && IGtQ[p,0] && Not[EqQ[m,3] && NeQ[p,1]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && igtq!(p_, 0)
                && !(eqq!(m_, 3) && neq!(p_, 1))
        },
        rhs: {
            let payload = (&d__ + &e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1108,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) -
          b*p/(d*e*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[p,0] && LtQ[m,-1] &&
          Not[IntegerQ[m/2] && LtQ[m+2*p+3,0]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            let m_2p_3 = &m_ + Atom::num(2) * &p_ + 3;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(m_2p_3, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && !(integerq!(&m_ / Atom::num(2)) && ltq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct =
                linear.pow(&m_ + 1) * quadratic.pow(&p_) / (&e__ * (&m_ + 1));
            let coefficient = &b__ * &p_ / (&d__ * &e__ * (&m_ + 1));
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ + 2) * quadratic.pow(&p_ - 1)), x_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1109,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) -
          d*p*(b^2-4*a*c)/(b*e*(m+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[p,0] &&
          Not[LtQ[m,-1]] && Not[IGtQ[(m-1)/2,0] && (Not[IntegerQ[p]] || LtQ[m,2*p])] && RationalQ[m] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            let m_2p_3 = &m_ + Atom::num(2) * &p_ + 3;
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(m_2p_3, 0)
                && gtq!(p_, 0)
                && !ltq!(m_, -1)
                && !(igtq!((&m_ - 1) / Atom::num(2), 0)
                    && (!integerq!(p_) || ltq!(m_, Atom::num(2) * &p_)))
                && rationalq!(m_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * &p_ + 1;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct = linear.pow(&m_ + 1) * quadratic.pow(&p_) / (&e__ * &balance);
            let coefficient = &d__ * &p_ * discriminant / (&b__ * &e__ * balance);
            let recursive = rubi_rhs_int(&(linear.pow(&m_) * quadratic.pow(&p_ - 1)), x_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1110,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) -
          d*e*(m-1)/(b*(p+1)) \\[Star] Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &d__ * linear.pow(&m_ - 1) * quadratic.pow(&p_ + 1)
                / (&b__ * (&p_ + 1));
            let coefficient = &d__ * &e__ * (&m_ - 1) / (&b__ * (&p_ + 1));
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ - 2) * quadratic.pow(&p_ + 1)), x_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1111,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) -
          2*c*e*(m+2*p+3)/(e*(p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[p,-1] && Not[GtQ[m,1]] && RationalQ[m] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && ltq!(p_, -1)
                && !gtq!(m_, 1)
                && rationalq!(m_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct = Atom::num(2) * &c__ * linear.pow(&m_ + 1)
                * quadratic.pow(&p_ + 1)
                / (&e__ * (&p_ + 1) * &discriminant);
            let coefficient = Atom::num(2)
                * &c__
                * &e__
                * (&m_ + Atom::num(2) * &p_ + 3)
                / (&e__ * (&p_ + 1) * discriminant);
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_) * quadratic.pow(&p_ + 1)), x_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1112,
        source: "Int[1/((d_+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          4*c \\[Star] Subst[Int[1/(b^2*e-4*a*c*e+4*c*e*x^2),x],x,Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed = rubi_rhs_int(
                &(Atom::num(1)
                    / (&b__.pow(2) * &e__ - Atom::num(4) * &a__ * &c__ * &e__
                        + Atom::num(4) * &c__ * &e__ * sub_atom.pow(2))),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &transformed,
                sub_symbol,
                (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt(),
            );
            rubi_star(Atom::num(4) * &c__, substituted)
        },
    ));
}

fn push_rules_rule_1113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1113,
        source: "Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          4/e*Sqrt[-c/(b^2-4*a*c)] \\[Star] Subst[Int[1/Sqrt[Simp[1-b^2*x^4/(d^2*(b^2-4*a*c)),x]],x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[c/(b^2-4*a*c),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && ltq!(&c__ / discriminant, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let radicand = rubi_simp(
                &(Atom::num(1)
                    - b__.pow(2) * sub_atom.pow(4)
                        / (d__.pow(2) * &discriminant)),
                sub_symbol,
            );
            let transformed =
                rubi_rhs_int(&(Atom::num(1) / radicand.sqrt()), sub_symbol);
            let substituted = substitute_symbol(
                &transformed,
                sub_symbol,
                (&d__ + &e__ * x_).sqrt(),
            );
            let coefficient =
                Atom::num(4) / &e__ * (-&c__ / discriminant).sqrt();
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_1114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1114,
        source: "Int[Sqrt[d_+e_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          4/e*Sqrt[-c/(b^2-4*a*c)] \\[Star] Subst[Int[x^2/Sqrt[Simp[1-b^2*x^4/(d^2*(b^2-4*a*c)),x]],x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[c/(b^2-4*a*c),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt() / (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && ltq!(&c__ / &discriminant, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let radicand = rubi_simp(
                &(Atom::num(1)
                    - b__.pow(2) * sub_atom.pow(4)
                        / (d__.pow(2) * &discriminant)),
                sub_symbol,
            );
            let transformed =
                rubi_rhs_int(&(sub_atom.pow(2) / radicand.sqrt()), sub_symbol);
            let substituted = substitute_symbol(
                &transformed,
                sub_symbol,
                (&d__ + &e__ * x_).sqrt(),
            );
            let coefficient =
                Atom::num(4) / &e__ * (-&c__ / discriminant).sqrt();
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_1115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1115,
        source: "Int[(d_+e_.*x_)^m_/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/Sqrt[a+b*x+c*x^2] \\[Star]
            Int[(d+e*x)^m/Sqrt[-a*c/(b^2-4*a*c)-b*c*x/(b^2-4*a*c)-c^2*x^2/(b^2-4*a*c)],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && EqQ[m^2,1/4]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let transformed_quadratic = -&a__ * &c__ / &discriminant
                - &b__ * &c__ * x_ / &discriminant
                - c__.pow(2) * x_.pow(2) / &discriminant;
            let recursive = rubi_rhs_int(
                &((&d__ + &e__ * x_).pow(&m_)
                    / transformed_quadratic.sqrt()),
                x_,
            );
            let coefficient =
                (-&c__ * &quadratic / discriminant).sqrt() / quadratic.sqrt();
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1116,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          2*d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(m+2*p+1)) +
          d^2*(m-1)*(b^2-4*a*c)/(b^2*(m+2*p+1)) \\[Star] Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[m,1] &&
          NeQ[m+2*p+1,0] && (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || OddQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            let balance1 = (&m_ + Atom::num(2) * &p_ + 1).expand();
            let balance3 = (&m_ + Atom::num(2) * &p_ + 3).expand();
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(balance3, 0)
                && gtq!(m_, 1)
                && neq!(balance1, 0)
                && (integerq!(Atom::num(2) * &p_)
                    || integerq!(m_) && rationalq!(p_)
                    || rubi_odd_q(&m_))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * &p_ + 1;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct = Atom::num(2) * &d__ * linear.pow(&m_ - 1)
                * quadratic.pow(&p_ + 1)
                / (&b__ * &balance);
            let coefficient = d__.pow(2) * (&m_ - 1) * discriminant
                / (b__.pow(2) * balance);
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ - 2) * quadratic.pow(&p_)), x_);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1117,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -2*b*d*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(d^2*(m+1)*(b^2-4*a*c)) +
          b^2*(m+2*p+3)/(d^2*(m+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[m,-1] &&
          (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || IntegerQ[(m+2*p+3)/2])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            let balance = (&m_ + Atom::num(2) * &p_ + 3).expand();
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && neq!(balance, 0)
                && ltq!(m_, -1)
                && (integerq!(Atom::num(2) * &p_)
                    || integerq!(m_) && rationalq!(p_)
                    || integerq!((&m_ + Atom::num(2) * &p_ + 3) / Atom::num(2)))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = d__.pow(2) * (&m_ + 1) * &discriminant;
            let direct = -Atom::num(2) * &b__ * &d__ * linear.pow(&m_ + 1)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let coefficient =
                b__.pow(2) * (&m_ + Atom::num(2) * &p_ + 3) / denominator;
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ + 2) * quadratic.pow(&p_)), x_);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1118,
        source: "Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          1/e \\[Star] Subst[Int[x^m*(a-b^2/(4*c)+(c*x^2)/e^2)^p,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[2*c*d-b*e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed = rubi_rhs_int(
                &(sub_atom.pow(&m_)
                    * (&a__ - b__.pow(2) / (Atom::num(4) * &c__)
                        + &c__ * sub_atom.pow(2) / e__.pow(2))
                    .pow(&p_)),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &transformed,
                sub_symbol,
                &d__ + &e__ * x_,
            );
            rubi_star(Atom::num(1) / &e__, substituted)
        },
    ));
}

fn push_rules_rule_1140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1140,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1141,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(d+e*x)^m*(b/2-q/2+c*x)^p*(b/2+q/2+c*x)^p,x],x] /;
         EqQ[p,-1] || Not[FractionalPowerFactorQ[q]]] /;
        FreeQ[{a,b,c,d,e},x] && ILtQ[p,0] && IntegerQ[m] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__], x_)
                && iltq!(p_, 0)
                && integerq!(m_)
                && rubi_nice_sqrt_q(&(b__.pow(2) - Atom::num(4) * &a__ * &c__))
                && (eqq!(p_, -1) || !rubi_fractional_power_factor_q(&q))
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&b__ / 2 - &q / 2 + &c__ * x_).pow(&p_)
                * (&b__ / 2 + &q / 2 + &c__ * x_).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1143,
        source: "Int[(d_.+e_.*x_)^m_/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m/(a+b*x+c*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m,1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && igtq!(m_, 1)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1145,
        source: "Int[(d_.+e_.*x_)^m_/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x)^(m+1)*Simp[c*d-b*e-c*e*x,x]/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && iltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let direct = &e__ * linear.pow(&m_ + 1) / ((&m_ + 1) * &invariant);
            let recursive_integrand = linear.pow(&m_ + 1)
                * rubi_simp(&(&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_), x_)
                / quadratic;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / invariant, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1146,
        source: "Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*(d+e*x)^(m-1)/(c*(m-1)) +
          1/c \\[Star] Int[(d+e*x)^(m-2)*Simp[c*d^2-a*e^2+e*(2*c*d-b*e)*x,x]/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && gtq!(m_, 1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &e__ * linear.pow(&m_ - 1) / (&c__ * (&m_ - 1));
            let recursive_integrand = linear.pow(&m_ - 2)
                * rubi_simp(
                    &(&c__ * d__.pow(2) - &a__ * e__.pow(2)
                        + &e__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_),
                    x_,
                )
                / quadratic;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / c__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1147,
        source: "Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x)^(m+1)*Simp[c*d-b*e-c*e*x,x]/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,m},x] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && ltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let direct = &e__ * linear.pow(&m_ + 1) / ((&m_ + 1) * &invariant);
            let recursive_integrand = linear.pow(&m_ + 1)
                * rubi_simp(&(&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_), x_)
                / quadratic;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / invariant, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1148,
        source: "Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          2*e \\[Star] Subst[Int[x^2/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt() / (a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2)
                - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * sub_atom.pow(2)
                + &c__ * sub_atom.pow(4);
            let transformed = rubi_rhs_int(
                &(sub_atom.pow(2) / transformed_denominator),
                sub_symbol,
            );
            let substitution = (&d__ + &e__ * x_).sqrt();

            rubi_star(Atom::num(2) * e__, rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1144,
        source: "Int[1/((d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
          e*Log[RemoveContent[d+e*x,x]]/(c*d^2-b*d*e+a*e^2) +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(c*d-b*e-c*e*x)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let second_numerator = &c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_;
            rubi_simp(&(&e__ * rubi_remove_content(&linear, x_).log() / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&(second_numerator / quadratic), x_))
        },
    ));
}

fn push_rules_rule_1149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1149,
        source: "Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
          2*e \\[Star] Subst[Int[1/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2)
                - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * sub_atom.pow(2)
                + &c__ * sub_atom.pow(4);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / transformed_denominator),
                sub_symbol,
            );
            let substitution = (&d__ + &e__ * x_).sqrt();

            rubi_star(Atom::num(2) * e__, rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1150,
        source: "Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m,1/(a+b*x+c*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && Not[IntegerQ[2*m]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && !integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let u = (&d__ + &e__ * x_).pow(&m_);
            let expanded_factor =
                Atom::num(1) / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&u, &expanded_factor, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1151,
        source: "Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^FracPart[p]*(a+b*x+c*x^2)^FracPart[p]/(a*d+c*e*x^3)^FracPart[p] \\[Star] Int[(d+e*x)^(m-p)*(a*d+c*e*x^3)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0] && IGtQ[m-p+1,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * &d__ + &a__ * &e__, 0)
                && eqq!(&c__ * &d__ + &b__ * &e__, 0)
                && igtq!((&m_ - &p_ + 1).expand(), 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let collapsed = &a__ * &d__ + &c__ * &e__ * x_.pow(3);
            let denominator = collapsed.pow(&frac_p);
            let recursive_integrand = linear.pow((&m_ - &p_).expand()) * collapsed.pow(&p_);
            rubi_star(linear.pow(&frac_p) * trinomial.pow(&frac_p) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1168,
        source: "Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
          Int[(d+e*x)^m/(Sqrt[b*x]*Sqrt[1+c/b*x]),x] /;
        FreeQ[{b,c,d,e},x] && NeQ[c*d-b*e,0] && EqQ[m^2,1/4] && LtQ[c,0] && RationalQ[b]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, m_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([b__, c__, d__, e__], x_)
                && neq!(&c__ * &d__ - &b__ * &e__, 0)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
                && ltq!(c__, 0)
                && rationalq!(b__)
        },
        rhs: {
            let transformed_integrand = (&d__ + &e__ * x_).pow(&m_)
                / ((&b__ * x_).sqrt()
                    * (Atom::num(1) + &c__ * x_ / &b__).sqrt());

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_1169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1169,
        source: "Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
          Sqrt[x]*Sqrt[b+c*x]/Sqrt[b*x+c*x^2] \\[Star] Int[(d+e*x)^m/(Sqrt[x]*Sqrt[b+c*x]),x] /;
        FreeQ[{b,c,d,e},x] && NeQ[c*d-b*e,0] && EqQ[m^2,1/4]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [b__, c__, d__, e__, m_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([b__, c__, d__, e__], x_)
                && neq!(&c__ * &d__ - &b__ * &e__, 0)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let transformed_integrand =
                linear.pow(&m_) / (x_.sqrt() * (&b__ + &c__ * x_).sqrt());
            rubi_star(x_.sqrt() * (&b__ + &c__ * x_).sqrt()
                    / (&b__ * x_ + &c__ * x_.pow(2)).sqrt(), rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 1170,
        source: "Int[x_^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
          2 \\[Star] Subst[Int[x^(2*m+1)/Sqrt[a+b*x^2+c*x^4],x],x,Sqrt[x]] /;
        FreeQ[{a,b,c},x] && EqQ[m^2,1/4]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) / (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = sub_atom.pow(Atom::num(2) * &m_ + 1)
                / (&a__ + &b__ * sub_atom.pow(2) + &c__ * sub_atom.pow(4)).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            rubi_star(Atom::num(2), rubi_subst(&transformed, sub_symbol, x_.sqrt()))
        },
    ));
}

fn push_rules_rule_1171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1171,
        source: "Int[(e_*x_)^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
          (e*x)^m/x^m \\[Star] Int[x^m/Sqrt[a+b*x+c*x^2], x] /;
        FreeQ[{a,b,c,e},x] && EqQ[m^2,1/4]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            / (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, e__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, e__], x_)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt();
            rubi_star((&e__ * x_).pow(&m_) / x_.pow(&m_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1172,
        source: "Int[(d_.+e_.*x_)^m_/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          2*Rt[b^2-4*a*c,2]*(d+e*x)^m*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/
            (c*Sqrt[a+b*x+c*x^2]*(2*c*(d+e*x)/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m) \\[Star]
            Subst[Int[(1+2*e*Rt[b^2-4*a*c,2]*x^2/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m/Sqrt[1-x^2],x],x,
              Sqrt[(b+Rt[b^2-4*a*c,2]+2*c*x)/(2*Rt[b^2-4*a*c,2])]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m^2,1/4]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(m_.pow(2), Atom::num(1) / Atom::num(4))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let den = Atom::num(2) * &c__ * &d__ - &b__ * &e__ - &e__ * &q;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = (Atom::num(1)
                + Atom::num(2) * &e__ * &q * sub_atom.pow(2) / &den)
                .pow(&m_)
                / (Atom::num(1) - sub_atom.pow(2)).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let scaled_linear = Atom::num(2) * &c__ * &linear / &den;
            let scaled_denominator = &c__ * &quadratic.sqrt() * scaled_linear.pow(&m_);
            let substitution =
                ((&b__ + &q + Atom::num(2) * &c__ * x_) / (Atom::num(2) * &q)).sqrt();
            let prefactor = Atom::num(2)
                * &q
                * linear.pow(&m_)
                * (-&c__ * &quadratic / discriminant).sqrt()
                / scaled_denominator;

            rubi_star(prefactor, rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1152,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -(d+e*x)^(m+1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^p/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) +
          p*(b^2-4*a*c)/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+2*p+2,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let k = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = Atom::num(2) * (&m_ + Atom::num(1)) * &k;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_numerator = &d__ * &b__ - Atom::num(2) * &a__ * &e__
                + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_;
            let direct = -linear.pow(&m_ + Atom::num(1))
                * direct_numerator
                * quadratic.pow(&p_)
                / &denominator;
            let recursive_integrand = linear.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_ - 1);
            rubi_simp(&(direct), x_) + rubi_star(&p_ * (b__.pow(2) - Atom::num(4) * &a__ * &c__) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1153,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
          2*(2*p+3)*(c*d^2-b*d*e+a*e^2)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+2*p+2,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let disc = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let k = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&p_ + Atom::num(1)) * &disc;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_numerator = &d__ * &b__ - Atom::num(2) * &a__ * &e__
                + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_;
            let direct = linear.pow(&m_ - Atom::num(1))
                * direct_numerator
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(2)) * quadratic.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(2) * (Atom::num(2) * &p_ + Atom::num(3)) * k
                    / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1154,
        source: "Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          -2 \\[Star] Subst[Int[1/(4*c*d^2-4*b*d*e+4*a*e^2-x^2),x],x,(2*a*e-b*d-(2*c*d-b*e)*x)/Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.266.1, CRC 258", "G&R 2.266.3, CRC 259"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / (Atom::num(4) * &c__ * d__.pow(2)
                    - Atom::num(4) * &b__ * &d__ * &e__
                    + Atom::num(4) * &a__ * e__.pow(2)
                    - sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let substitution = (Atom::num(2) * &a__ * &e__
                - &b__ * &d__
                - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                / quadratic.sqrt();

            rubi_star(Atom::num(-2), rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1155,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(b-q+2*c*x)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/
            ((m+1)*(2*c*d-b*e+e*q)*((2*c*d-b*e+e*q)*(b+q+2*c*x)/((2*c*d-b*e-e*q)*(b-q+2*c*x)))^p)*
            Hypergeometric2F1[m+1,-p,m+2,-4*c*q*(d+e*x)/((2*c*d-b*e-e*q)*(b-q+2*c*x))]] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[m+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let m1 = &m_ + Atom::num(1);
            let t_plus = Atom::num(2) * &c__ * &d__ - &b__ * &e__ + &e__ * &q;
            let t_minus = Atom::num(2) * &c__ * &d__ - &b__ * &e__ - &e__ * &q;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_linear = &b__ - &q + Atom::num(2) * &c__ * x_;
            let second_linear = &b__ + &q + Atom::num(2) * &c__ * x_;
            let denominator_power = (&t_plus * &second_linear) / (&t_minus * &first_linear);
            let denominator = &m1 * &t_plus * denominator_power.pow(&p_);
            let hyper_argument =
                -Atom::num(4) * &c__ * &q * &linear / (&t_minus * &first_linear);

            rubi_simp(&(-first_linear * linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_)
                    / denominator
                    * rubi_hypergeometric2f1(
                        &m_ + Atom::num(1),
                        -&p_,
                        &m_ + Atom::num(2),
                        hyper_argument,
                    )), x_)
        },
    ));
}

fn push_rules_rule_1156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1156,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) +
          m*(2*c*d-b*e)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[m+2*p+3,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let linear_coefficient = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let denominator = &p1 * &discriminant;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = linear.pow(&m_)
                * (&b__ + Atom::num(2) * &c__ * x_)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_) + rubi_star(&m_ * linear_coefficient / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1157,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          (2*c*d-b*e)/(2*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[m+2*p+3,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &e__ * linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1))
                / (&m1 * &invariant);
            let recursive_integrand =
                linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                    / (Atom::num(2) * invariant), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1161,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) -
          p/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && GtQ[p,0] && (IntegerQ[p] || LtQ[m,-1]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && gtq!(p_, 0)
                && (integerq!(p_) || ltq!(m_, -1))
                && neq!(m_, -1)
                && !iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let denominator = &e__ * &m1;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) / &denominator;
            let recursive_integrand = linear.pow(&m_ + Atom::num(1))
                * (&b__ + Atom::num(2) * &c__ * x_)
                * quadratic.pow(&p_ - Atom::num(1));
            rubi_simp(&(direct), x_) - rubi_star(&p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1162,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) -
          p/(e*(m+2*p+1)) \\[Star] Int[(d+e*x)^m*Simp[b*d-2*a*e+(2*c*d-b*e)*x,x]*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && GtQ[p,0] && NeQ[m+2*p+1,0] && (Not[RationalQ[m]] || LtQ[m,1]) && Not[ILtQ[m+2*p,0]] && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && (!rationalq!(m_) || ltq!(m_, 1))
                && !iltq!(&m_ + Atom::num(2) * &p_, 0)
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let denominator_factor = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let denominator = &e__ * &denominator_factor;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) / &denominator;
            let payload = simp!(
                &b__ * &d__ - Atom::num(2) * &a__ * &e__
                    + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_,
                x_
            );
            let recursive_integrand =
                linear.pow(&m_) * payload * quadratic.pow(&p_ - Atom::num(1));
            rubi_simp(&(direct), x_) - rubi_star(&p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1163,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(b*e*m+2*c*d*(2*p+3)+2*c*e*(m+2*p+3)*x)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[p,-1] && GtQ[m,0] && (LtQ[m,1] || ILtQ[m+2*p+3,0] && NeQ[m,2]) && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && (ltq!(m_, 1)
                    || iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0) && neq!(m_, 2))
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let raised_p = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &raised_p * &discriminant;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = linear.pow(&m_)
                * (&b__ + Atom::num(2) * &c__ * x_)
                * quadratic.pow(&raised_p)
                / &denominator;
            let payload = &b__ * &e__ * &m_
                + Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3))
                + Atom::num(2)
                    * &c__
                    * &e__
                    * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                    * x_;
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(1)) * payload * quadratic.pow(&raised_p);
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1164,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d+e*x)^(m-2)*
              Simp[e*(2*a*e*(m-1)+b*d*(2*p-m+4))-2*c*d^2*(2*p+3)+e*(b*e-2*d*c)*(m+2*p+2)*x,x]*
              (a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[p,-1] && GtQ[m,1] && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let raised_p = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &raised_p * &discriminant;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = linear.pow(&m_ - Atom::num(1))
                * (&d__ * &b__ - Atom::num(2) * &a__ * &e__
                    + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                * quadratic.pow(&raised_p)
                / &denominator;
            let payload = simp!(
                &e__ * (Atom::num(2) * &a__ * &e__ * (&m_ - Atom::num(1))
                    + &b__ * &d__ * (Atom::num(2) * &p_ - &m_ + Atom::num(4)))
                    - Atom::num(2) * &c__ * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(3))
                    + &e__
                        * (&b__ * &e__ - Atom::num(2) * &d__ * &c__)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(2))
                        * x_,
                x_
            );
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(2)) * payload * quadratic.pow(&raised_p);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1165,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(b*c*d-b^2*e+2*a*c*e+c*(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) +
          1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) \\[Star]
            Int[(d+e*x)^m*
              Simp[b*c*d*e*(2*p-m+2)+b^2*e^2*(m+p+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3)-c*e*(2*c*d-b*e)*(m+2*p+4)*x,x]*
              (a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && LtQ[p,-1] && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && ltq!(p_, -1)
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let raised_p = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = &raised_p * &discriminant * &invariant;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_payload = &b__ * &c__ * &d__ - b__.pow(2) * &e__
                + Atom::num(2) * &a__ * &c__ * &e__
                + &c__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_;
            let direct = linear.pow(&m_ + Atom::num(1))
                * direct_payload
                * quadratic.pow(&raised_p)
                / &denominator;
            let payload = simp!(
                &b__ * &c__ * &d__ * &e__ * (Atom::num(2) * &p_ - &m_ + Atom::num(2))
                    + b__.pow(2) * e__.pow(2) * (&m_ + &p_ + Atom::num(2))
                    - Atom::num(2) * c__.pow(2) * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(3))
                    - Atom::num(2)
                        * &a__
                        * &c__
                        * e__.pow(2)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                    - &c__
                        * &e__
                        * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                        * x_,
                x_
            );
            let recursive_integrand = linear.pow(&m_) * payload * quadratic.pow(&raised_p);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1166,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) +
          1/(c*(m+2*p+1)) \\[Star]
            Int[(d+e*x)^(m-2)*
              Simp[c*d^2*(m+2*p+1)-e*(a*e*(m-1)+b*d*(p+1))+e*(2*c*d-b*e)*(m+p)*x,x]*
              (a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && If[RationalQ[m], GtQ[m,1], SumSimplerQ[m,-2]] && NeQ[m+2*p+1,0] && IntQuadraticQ[a,b,c,d,e,m,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && if rationalq!(m_) {
                    gtq!(m_, 1)
                } else {
                    rubi_sum_simpler_q(&m_, &Atom::num(-2))
                }
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
        },
        rhs: {
            let denominator_factor = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let denominator = &c__ * &denominator_factor;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct =
                &e__ * linear.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1))
                    / &denominator;
            let payload = simp!(
                &c__ * d__.pow(2) * &denominator_factor
                    - &e__
                        * (&a__ * &e__ * (&m_ - Atom::num(1))
                            + &b__ * &d__ * (&p_ + Atom::num(1)))
                    + &e__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * (&m_ + &p_) * x_,
                x_
            );
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(2)) * payload * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1167,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star]
            Int[(d+e*x)^(m+1)*Simp[c*d*(m+1)-b*e*(m+p+2)-c*e*(m+2*p+3)*x,x]*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[m,-1] && (LtQ[m,-1] && IntQuadraticQ[a,b,c,d,e,m,p,x] || SumSimplerQ[m,1] && IntegerQ[p] || ILtQ[Simplify[m+2*p+3],0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            let shifted = (&m_ + Atom::num(2) * &p_ + Atom::num(3)).expand();
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(m_, -1)
                && (ltq!(m_, -1) && int_quadratic_q(&a__, &b__, &c__, &d__, &e__, &m_, &p_)
                    || rubi_sum_simpler_q(&m_, &Atom::num(1)) && integerq!(p_)
                    || iltq!(shifted, 0))
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = &m1 * &invariant;
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct =
                &e__ * linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1))
                    / &denominator;
            let payload = simp!(
                &c__ * &d__ * &m1
                    - &b__ * &e__ * (&m_ + &p_ + Atom::num(2))
                    - &c__ * &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_,
                x_
            );
            let recursive_integrand =
                linear.pow(&m_ + Atom::num(1)) * payload * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1173,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          1/(-4*c/(b^2-4*a*c))^p \\[Star] Subst[Int[Simp[1-x^2/(b^2-4*a*c),x]^p/Simp[2*c*d-b*e+e*x,x],x],x,b+2*c*x] /;
        FreeQ[{a,b,c,d,e,p},x] && GtQ[4*a-b^2/c,0] && IntegerQ[4*p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            let test = Atom::num(4) * &a__ - b__.pow(2) / &c__;
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && gtq!(test, 0)
                && integerq!(Atom::num(4) * &p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let scale = -Atom::num(4) * &c__ / &discriminant;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = simp!(
                Atom::num(1) - sub_atom.pow(2) / &discriminant,
                sub_symbol
            )
            .pow(&p_)
                / simp!(
                    Atom::num(2) * &c__ * &d__ - &b__ * &e__ + &e__ * &sub_atom,
                    sub_symbol
                );
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            let substitution = b__ + Atom::num(2) * c__ * x_;

            rubi_star(Atom::num(1) / scale.pow(&p_), rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 1174,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          (a+b*x+c*x^2)^p/(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^p \\[Star]
            Int[(-a*c/(b^2-4*a*c)-b*c*x/(b^2-4*a*c)-c^2*x^2/(b^2-4*a*c))^p/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,p},x] && Not[GtQ[4*a-b^2/c,0]] && IntegerQ[4*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            let test = Atom::num(4) * &a__ - b__.pow(2) / &c__;
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && !gtq!(test, 0)
                && integerq!(Atom::num(4) * &p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let scale_base = -&c__ * &quadratic / &discriminant;
            let transformed_base = -&a__ * &c__ / &discriminant
                - &b__ * &c__ * x_ / &discriminant
                - c__.pow(2) * x_.pow(2) / &discriminant;
            let recursive_integrand = transformed_base.pow(&p_) / (&d__ + &e__ * x_);
            rubi_star(quadratic.pow(&p_) / scale_base.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1175,
        source: "Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
          With[{q=Rt[3*c*e^2*(2*c*d-b*e),3]},
          -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]+2*(c*d-b*e-c*e*x)/(Sqrt[3]*q*(a+b*x+c*x^2)^(1/3))]/q^2 -
          3*c*e*Log[d+e*x]/(2*q^2) +
          3*c*e*Log[c*d-b*e-c*e*x-q*(a+b*x+c*x^2)^(1/3)]/(2*q^2)] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2-b*c*d*e+b^2*e^2-3*a*c*e^2,0] && PosQ[c*e^2*(2*c*d-b*e)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            let balance = c__.pow(2) * d__.pow(2)
                - &b__ * &c__ * &d__ * &e__
                + b__.pow(2) * e__.pow(2)
                - Atom::num(3) * &a__ * &c__ * e__.pow(2);
            let positivity = &c__ * e__.pow(2) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__);
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(balance, 0)
                && posq!(positivity)
        },
        rhs: {
            let q = rubi_rt(
                &(Atom::num(3) * &c__ * e__.pow(2) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)),
                3,
            );
            let sqrt_three = Atom::num(3).sqrt();
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let radical = quadratic.pow(Atom::num(1) / Atom::num(3));
            let q_squared = q.pow(2);
            let atan_argument = Atom::num(1) / &sqrt_three
                + Atom::num(2) * (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)
                    / (&sqrt_three * &q * &radical);
            let log_argument = &c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_ - &q * radical;

            rubi_simp(&(-&sqrt_three * &c__ * &e__ * atan_argument.atan() / &q_squared), x_)
                    - rubi_simp(&(Atom::num(3) * &c__ * &e__ * (&d__ + &e__ * x_).log()
                        / (Atom::num(2) * &q_squared)), x_)
                    + rubi_simp(&(Atom::num(3) * c__ * e__ * log_argument.log()
                        / (Atom::num(2) * q_squared)), x_)
        },
    ));
}

fn push_rules_rule_1176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1176,
        source: "Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
          With[{q=Rt[-3*c*e^2*(2*c*d-b*e),3]},
          -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]-2*(c*d-b*e-c*e*x)/(Sqrt[3]*q*(a+b*x+c*x^2)^(1/3))]/q^2 -
          3*c*e*Log[d+e*x]/(2*q^2) +
          3*c*e*Log[c*d-b*e-c*e*x+q*(a+b*x+c*x^2)^(1/3)]/(2*q^2)] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2-b*c*d*e+b^2*e^2-3*a*c*e^2,0] && NegQ[c*e^2*(2*c*d-b*e)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            let balance = c__.pow(2) * d__.pow(2)
                - &b__ * &c__ * &d__ * &e__
                + b__.pow(2) * e__.pow(2)
                - Atom::num(3) * &a__ * &c__ * e__.pow(2);
            let negativity = &c__ * e__.pow(2) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__);
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(balance, 0)
                && negq!(negativity)
        },
        rhs: {
            let q = rubi_rt(
                &(-Atom::num(3) * &c__ * e__.pow(2) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)),
                3,
            );
            let sqrt_three = Atom::num(3).sqrt();
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let radical = quadratic.pow(Atom::num(1) / Atom::num(3));
            let q_squared = q.pow(2);
            let atan_argument = Atom::num(1) / &sqrt_three
                - Atom::num(2) * (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)
                    / (&sqrt_three * &q * &radical);
            let log_argument = &c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_ + &q * radical;

            rubi_simp(&(-&sqrt_three * &c__ * &e__ * atan_argument.atan() / &q_squared), x_)
                    - rubi_simp(&(Atom::num(3) * &c__ * &e__ * (&d__ + &e__ * x_).log()
                        / (Atom::num(2) * &q_squared)), x_)
                    + rubi_simp(&(Atom::num(3) * c__ * e__ * log_argument.log()
                        / (Atom::num(2) * q_squared)), x_)
        },
    ));
}

fn push_rules_rule_1177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1177,
        source: "Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (b+q+2*c*x)^(1/3)*(b-q+2*c*x)^(1/3)/(a+b*x+c*x^2)^(1/3) \\[Star] Int[1/((d+e*x)*(b+q+2*c*x)^(1/3)*(b-q+2*c*x)^(1/3)),x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d^2-b*c*d*e-2*b^2*e^2+9*a*c*e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            let balance = c__.pow(2) * d__.pow(2)
                - &b__ * &c__ * &d__ * &e__
                - Atom::num(2) * b__.pow(2) * e__.pow(2)
                + Atom::num(9) * &a__ * &c__ * e__.pow(2);
            freeq!([a__, b__, c__, d__, e__], x_) && eqq!(balance, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first = (&b__ + &q + Atom::num(2) * &c__ * x_)
                .pow(Atom::num(1) / Atom::num(3));
            let second = (&b__ - &q + Atom::num(2) * &c__ * x_)
                .pow(Atom::num(1) / Atom::num(3));
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand =
                Atom::num(1) / ((&d__ + &e__ * x_) * &first * &second);
            rubi_star(first * second / quadratic.pow(Atom::num(1) / Atom::num(3)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1178,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(1/(d+e*x))^(2*p)*(a+b*x+c*x^2)^p/(e*(e*(b-q+2*c*x)/(2*c*(d+e*x)))^p*(e*(b+q+2*c*x)/(2*c*(d+e*x)))^p) \\[Star]
            Subst[Int[x^(-m-2*(p+1))*Simp[1-(d-e*(b-q)/(2*c))*x,x]^p*Simp[1-(d-e*(b+q)/(2*c))*x,x]^p,x],x,1/(d+e*x)]] /;
        FreeQ[{a,b,c,d,e,p},x] && ILtQ[m,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_) && iltq!(m_, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_linear = &b__ - &q + Atom::num(2) * &c__ * x_;
            let second_linear = &b__ + &q + Atom::num(2) * &c__ * x_;
            let first_scale = &e__ * first_linear / (Atom::num(2) * &c__ * &linear);
            let second_scale = &e__ * second_linear / (Atom::num(2) * &c__ * &linear);
            let prefactor = -((Atom::num(1) / &linear).pow(Atom::num(2) * &p_))
                * quadratic.pow(&p_)
                / (&e__ * first_scale.pow(&p_) * second_scale.pow(&p_));

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = (-&m_ - Atom::num(2) * (&p_ + Atom::num(1))).expand();
            let first_simp = simp!(
                Atom::num(1) - (&d__ - &e__ * (&b__ - &q) / (Atom::num(2) * &c__)) * &sub_atom,
                sub
            );
            let second_simp = simp!(
                Atom::num(1) - (&d__ - &e__ * (&b__ + &q) / (Atom::num(2) * &c__)) * &sub_atom,
                sub
            );
            let transformed_integrand =
                sub_atom.pow(transformed_power) * first_simp.pow(&p_) * second_simp.pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substitution = Atom::num(1) / linear;

            rubi_star(prefactor, rubi_subst(&transformed, sub, substitution))
        },
    ));
}

fn push_rules_rule_1179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1179,
        source: "Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (a+b*x+c*x^2)^p/(e*(1-(d+e*x)/(d-e*(b-q)/(2*c)))^p*(1-(d+e*x)/(d-e*(b+q)/(2*c)))^p) \\[Star]
            Subst[Int[x^m*Simp[1-x/(d-e*(b-q)/(2*c)),x]^p*Simp[1-x/(d-e*(b+q)/(2*c)),x]^p,x],x,d+e*x]] /;
        FreeQ[{a,b,c,d,e,m,p},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let first_base = &d__ - &e__ * (&b__ - &q) / (Atom::num(2) * &c__);
            let second_base = &d__ - &e__ * (&b__ + &q) / (Atom::num(2) * &c__);

            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let prefactor = quadratic.pow(&p_)
                / (&e__
                    * (Atom::num(1) - &linear / &first_base).pow(&p_)
                    * (Atom::num(1) - &linear / &second_base).pow(&p_));

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let first_simp = simp!(Atom::num(1) - &sub_atom / &first_base, sub);
            let second_simp = simp!(Atom::num(1) - &sub_atom / &second_base, sub);
            let transformed_integrand =
                sub_atom.pow(&m_) * first_simp.pow(&p_) * second_simp.pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(prefactor, rubi_subst(&transformed, sub, linear))
        },
    ));
}

fn push_rules_rule_1180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, u_);
    let rule = rubi_rule!(
        order: 1180,
        source: "Int[(d_.+e_.*u_)^m_.*(a_+b_.*u_+c_.*u_^2)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x,u] /;
        FreeQ[{a,b,c,d,e,m,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * u_).pow(m_) * (a__ + b__ * u_ + c__ * u_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, u_, m_, p_, x_],
        optional: [b__, c__, d__, e__, m_, p_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        x_linear: [u_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * &sub_atom).pow(&m_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, sub, u_))
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) / (a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) / (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) / (b__ * x_ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_) / (a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(Atom::num(1) / Atom::num(3)))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / ((d__ + e__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt())
}
