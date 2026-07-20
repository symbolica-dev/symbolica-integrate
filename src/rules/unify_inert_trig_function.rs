use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1(rules);
    push_rules_rule_2(rules);
    push_rules_rule_3(rules);
    push_rules_rule_4(rules);
    push_rules_rule_5(rules);
    push_rules_rule_6(rules);
    push_rules_rule_7(rules);
    push_rules_rule_8(rules);
    push_rules_rule_9(rules);
    push_rules_rule_10(rules);
    push_rules_rule_11(rules);
    push_rules_rule_12(rules);
    push_rules_rule_13(rules);
    push_rules_rule_14(rules);
    push_rules_rule_15(rules);
    push_rules_rule_16(rules);
    push_rules_rule_17(rules);
    push_rules_rule_18(rules);
    push_rules_rule_19(rules);
    push_rules_rule_20(rules);
    push_rules_rule_21(rules);
    push_rules_rule_22(rules);
    push_rules_rule_23(rules);
    push_rules_rule_24(rules);
    push_rules_rule_25(rules);
    push_rules_rule_26(rules);
    push_rules_rule_27(rules);
    push_rules_rule_28(rules);
    push_rules_rule_29(rules);
    push_rules_rule_30(rules);
    push_rules_rule_31(rules);
    push_rules_rule_32(rules);
    push_rules_rule_33(rules);
    push_rules_rule_34(rules);
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
}

fn push_rules_rule_1(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, u__);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 1,
        source: "UnifyInertTrigFunction[a_*u_,x_]",
        pattern: a__ * u__,
        head: head,
        with: [a__, u__, x_],
        when: { freeq!(a__, x_) },
        rhs: { a__ * rubi_unify_inert_trig_function(&u__, x_) },
    ));
}

fn push_rules_rule_2(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 2,
        source: "UnifyInertTrigFunction[(a_.*cos[e_.+f_.*x_])^m_.*(b_.*csc[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_cos(e__ + f__ * x_)).pow(m_) * (b__ * i_csc(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_sin(&angle)).pow(&m_) * (-&b__ * i_sec(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_3(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 3,
        source: "UnifyInertTrigFunction[(a_.*cos[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_cos(e__ + f__ * x_)).pow(m_) * (b__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_sin(&angle)).pow(&m_) * (&b__ * i_csc(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_4(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 4,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, n_, x_],
        optional: [a__, b__, e__, f__, n_],
        when: { freeq!([a__, b__, e__, f__, n_], x_) },
        rhs: {
            (&a__ + &b__ * i_sin(&e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_)).pow(&n_)
        },
    ));
}

fn push_rules_rule_5(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 5,
        source: "UnifyInertTrigFunction[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_sin(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&g__ * i_cos(&angle)).pow(&p_) * (&a__ - &b__ * i_sin(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_6(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 6,
        source: "UnifyInertTrigFunction[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_csc(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&g__ * i_sec(&angle)).pow(&p_) * (&a__ - &b__ * i_sin(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_7(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 7,
        source: "UnifyInertTrigFunction[(g_.*cot[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_cot(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&g__ * i_tan(&angle)).pow(&p_) * (&a__ - &b__ * i_sin(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_8(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 8,
        source: "UnifyInertTrigFunction[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*cos[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_tan(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&g__ * i_cot(&angle)).pow(&p_) * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_9(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 9,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_10(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 10,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_csc(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_11(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 11,
        source: "UnifyInertTrigFunction[(g_.*sin[e_.+f_. x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_sin(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            if integerq!(Atom::num(2) * &p_) && ltq!(p_, 0) && integerq!(Atom::num(2) * &n_) {
                let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
                let sine = i_sin(&angle);
                (&g__ * i_cos(&angle)).pow(&p_)
                    * (&a__ - &b__ * &sine).pow(&m_)
                    * (&c__ - &d__ * sine).pow(&n_)
            } else {
                let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
                let sine = i_sin(&angle);
                (-&g__ * i_cos(&angle)).pow(&p_)
                    * (&a__ + &b__ * &sine).pow(&m_)
                    * (&c__ + &d__ * sine).pow(&n_)
            }
        },
    ));
}

fn push_rules_rule_12(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 12,
        source: "UnifyInertTrigFunction[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_csc(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&g__ * i_sec(&angle)).pow(&p_)
                * (&a__ - &b__ * &sine).pow(&m_)
                * (&c__ - &d__ * sine).pow(&n_)
        },
    ));
}

fn push_rules_rule_13(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 13,
        source: "UnifyInertTrigFunction[(g_.*cos[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&g__ * &sine).pow(&p_)
                * (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * sine).pow(&n_)
        },
    ));
}

fn push_rules_rule_14(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 14,
        source: "UnifyInertTrigFunction[(g_.*cos[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&g__ * &sine).pow(&p_)
                * (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * i_csc(angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_15(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 15,
        source: "UnifyInertTrigFunction[(g_.*sec[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&g__ * i_csc(angle)).pow(&p_)
                * (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * sine).pow(&n_)
        },
    ));
}

fn push_rules_rule_16(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 16,
        source: "UnifyInertTrigFunction[(g_.*sec[e_.+f_.*x_])^p_.*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&g__ * i_csc(&angle)).pow(&p_)
                * (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * i_csc(angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_17(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        capital_a__,
        capital_b__,
        m_,
        n_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 17,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_cos(e__ + f__ * x_)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * &sine).pow(&n_)
                * (&capital_a__ + &capital_b__ * sine)
        },
    ));
}

fn push_rules_rule_18(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        e__,
        f__,
        capital_a__,
        capital_b__,
        capital_c__,
        m_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 18,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_b__ * i_cos(e__ + f__ * x_) + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&a__ + &b__ * &sine).pow(&m_)
                * (&capital_a__ + &capital_b__ * &sine + &capital_c__ * sine.pow(2))
        },
    ));
}

fn push_rules_rule_19(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, capital_a__, capital_c__, m_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 19,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_c__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_c__, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&a__ + &b__ * &sine).pow(&m_) * (&capital_a__ + &capital_c__ * sine.pow(2))
        },
    ));
}

fn push_rules_rule_20(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        capital_a__,
        capital_b__,
        capital_c__,
        m_,
        n_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 20,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_cos(e__ + f__ * x_) + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_b__, capital_c__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * &sine).pow(&n_)
                * (&capital_a__ + &capital_b__ * &sine + &capital_c__ * sine.pow(2))
        },
    ));
}

fn push_rules_rule_21(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        capital_a__,
        capital_c__,
        m_,
        n_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 21,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_cos(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a__, capital_c__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&a__ + &b__ * &sine).pow(&m_)
                * (&c__ + &d__ * &sine).pow(&n_)
                * (&capital_a__ + &capital_c__ * sine.pow(2))
        },
    ));
}

fn push_rules_rule_22(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 22,
        source: "UnifyInertTrigFunction[(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_,x_]",
        pattern: (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [a__, b__, c__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_23(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 23,
        source: "UnifyInertTrigFunction[(d_.*cos[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine = i_sin(&angle);
            (&d__ * &sine).pow(&m_) * (&a__ + &b__ * (&c__ * sine).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_24(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 24,
        source: "UnifyInertTrigFunction[(d_.*sin[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cos(&angle)).pow(&m_)
                * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_25(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 25,
        source: "UnifyInertTrigFunction[(d_.*cot[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_tan(&angle)).pow(&m_)
                * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_26(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 26,
        source: "UnifyInertTrigFunction[(d_.*tan[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_tan(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cot(&angle)).pow(&m_)
                * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_27(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 27,
        source: "UnifyInertTrigFunction[(d_.*csc[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_sec(&angle)).pow(&m_)
                * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_28(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 28,
        source: "UnifyInertTrigFunction[(d_.*sec[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cos[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cos(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_csc(&angle)).pow(&m_)
                * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_29(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, capital_a_, capital_b_, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 29,
        source: "UnifyInertTrigFunction[(a_.+b_.*cos[e_.+f_.*x_]^n_)^m_.*(A_.+B_.*cos[e_.+f_.*x_]^n_),x_]",
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_).pow(n_)).pow(m_)
            * (capital_a_ + capital_b_ * i_cos(e__ + f__ * x_).pow(n_)),
        head: head,
        with: [a__, b__, e__, f__, n_, m_, capital_a_, capital_b_, x_],
        optional: [a__, b__, e__, f__, capital_a_, capital_b_],
        when: {
            freeq!([a__, b__, e__, f__, capital_a_, capital_b_, m_, n_], x_)
                && !(eqq!(a__, 0) && integerq!(m_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let sine_power = i_sin(&angle).pow(&n_);
            (&a__ + &b__ * &sine_power).pow(&m_) * (&capital_a_ + &capital_b_ * sine_power)
        },
    ));
}

fn push_rules_rule_30(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 30,
        source: "UnifyInertTrigFunction[(a_.*cos[e_.+f_.*x_])^m_.*(b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_cos(e__ + f__ * x_)).pow(m_) * (b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_sin(&angle)).pow(&m_) * (-&b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_31(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 31,
        source: "UnifyInertTrigFunction[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_sin(e__ + f__ * x_)).pow(m_) * (b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_cos(&angle)).pow(&m_) * (-&b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_32(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 32,
        source: "UnifyInertTrigFunction[(a_.*csc[e_.+f_.*x_])^m_.*(b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_csc(e__ + f__ * x_)).pow(m_) * (b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_sec(&angle)).pow(&m_) * (-&b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_33(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 33,
        source: "UnifyInertTrigFunction[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ * i_sec(e__ + f__ * x_)).pow(m_) * (b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ * i_csc(&angle)).pow(&m_) * (-&b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_34(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 34,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, n_, x_],
        optional: [a__, b__, e__, f__, n_],
        when: { freeq!([a__, b__, e__, f__, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ - &b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_35(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 35,
        source: "UnifyInertTrigFunction[(d_.*csc[e_.+f_.*x_])^m_.*(a_+b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, n_, x_],
        optional: [d__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_sec(&angle)).pow(&m_) * (&a__ - &b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_36(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 36,
        source: "UnifyInertTrigFunction[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, n_, x_],
        optional: [d__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_cos(&angle)).pow(&m_) * (&a__ - &b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_37(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 37,
        source: "UnifyInertTrigFunction[(d_.*cos[e_.+f_.*x_])^m_.*(a_+b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (d__ * i_cos(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, n_, x_],
        optional: [d__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_sin(&angle)).pow(&m_) * (&a__ - &b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_38(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 38,
        source: "UnifyInertTrigFunction[(d_.*sec[e_.+f_.*x_])^m_.*(a_+b_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (d__ * i_sec(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, n_, x_],
        optional: [d__, e__, f__, m_, b__, n_],
        when: { freeq!([a__, b__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_csc(&angle)).pow(&m_) * (&a__ - &b__ * i_tan(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_39(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 39,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_) * (&c__ - &d__ * tangent).pow(&n_)
        },
    ));
}

fn push_rules_rule_40(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 40,
        source: "UnifyInertTrigFunction[(g_.*cot[e_.+f_.*x_])^p_.*(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_cot(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cot(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (-&g__ * &tangent).pow(&p_)
                * (&a__ - &b__ * &tangent).pow(&m_)
                * (&c__ - &d__ * tangent).pow(&n_)
        },
    ));
}

fn push_rules_rule_41(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 41,
        source: "UnifyInertTrigFunction[(g_.*cot[e_.+f_.*x_])^p_.*(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*tan[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_cot(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_tan(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&g__ * i_tan(&angle)).pow(&p_)
                * (&a__ - &b__ * i_tan(&angle)).pow(&m_)
                * (&c__ - &d__ * i_cot(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_42(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, m_, n_, x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 42,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]),x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cot(e__ + f__ * x_)).pow(n_)
            * (capital_a_ + capital_b_ * i_cot(e__ + f__ * x_)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_)
                * (&c__ - &d__ * &tangent).pow(&n_)
                * (&capital_a_ - &capital_b_ * tangent)
        },
    ));
}

fn push_rules_rule_43(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, e__, f__, capital_a_, capital_b_, capital_c_, m_, x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 43,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (capital_a_ + capital_b_ * i_cot(e__ + f__ * x_) + capital_c_ * i_cot(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a_, capital_b_, capital_c_, x_],
        optional: [a__, b__, e__, f__, m_, capital_a_, capital_b_, capital_c_],
        when: { freeq!([a__, b__, e__, f__, capital_a_, capital_b_, capital_c_, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_)
                * (&capital_a_ - &capital_b_ * &tangent + &capital_c_ * tangent.pow(2))
        },
    ));
}

fn push_rules_rule_44(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, capital_a_, capital_c_, m_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 44,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (capital_a_ + capital_c_ * i_cot(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a_, capital_c_, x_],
        optional: [a__, b__, e__, f__, m_, capital_a_, capital_c_],
        when: { freeq!([a__, b__, e__, f__, capital_a_, capital_c_, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_) * (&capital_a_ + &capital_c_ * tangent.pow(2))
        },
    ));
}

fn push_rules_rule_45(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, capital_c_, m_, n_, x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 45,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+B_.*cot[e_.+f_.*x_]+C_.*cot[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cot(e__ + f__ * x_)).pow(n_)
            * (capital_a_ + capital_b_ * i_cot(e__ + f__ * x_) + capital_c_ * i_cot(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_, capital_c_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_, capital_c_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, capital_c_, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_)
                * (&c__ - &d__ * &tangent).pow(&n_)
                * (&capital_a_ - &capital_b_ * &tangent + &capital_c_ * tangent.pow(2))
        },
    ));
}

fn push_rules_rule_46(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_a_, capital_c_, m_, n_, x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 46,
        source: "UnifyInertTrigFunction[(a_.+b_.*cot[e_.+f_.*x_])^m_.*(c_.+d_.*cot[e_.+f_.*x_])^n_.*(A_.+C_.*cot[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cot(e__ + f__ * x_)).pow(n_)
            * (capital_a_ + capital_c_ * i_cot(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_c_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_c_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_c_, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let tangent = i_tan(&angle);
            (&a__ - &b__ * &tangent).pow(&m_)
                * (&c__ - &d__ * &tangent).pow(&n_)
                * (&capital_a_ + &capital_c_ * tangent.pow(2))
        },
    ));
}

fn push_rules_rule_47(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 47,
        source: "UnifyInertTrigFunction[(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_,x_]",
        pattern: (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [a__, b__, c__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_48(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 48,
        source: "UnifyInertTrigFunction[(d_.*cos[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_sin(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_49(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 49,
        source: "UnifyInertTrigFunction[(d_.*sin[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cos(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_50(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 50,
        source: "UnifyInertTrigFunction[(d_.*cot[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_tan(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_51(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 51,
        source: "UnifyInertTrigFunction[(d_.*tan[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_tan(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cot(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_52(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 52,
        source: "UnifyInertTrigFunction[(d_.*csc[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_sec(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_53(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 53,
        source: "UnifyInertTrigFunction[(d_.*sec[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*cot[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_cot(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_csc(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_tan(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_54(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 54,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, n_, x_],
        optional: [a__, b__, e__, f__, n_],
        when: { freeq!([a__, b__, e__, f__, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * i_csc(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_55(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 55,
        source: "UnifyInertTrigFunction[(g_.*sec[e_.+f_.*x_])^p_.*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&g__ * i_csc(&angle)).pow(&p_) * (&a__ + &b__ * i_csc(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_56(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 56,
        source: "UnifyInertTrigFunction[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_sin(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&g__ * i_cos(&angle)).pow(&p_) * (&a__ - &b__ * i_csc(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_57(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 57,
        source: "UnifyInertTrigFunction[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_csc(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&g__ * i_sec(&angle)).pow(&p_) * (&a__ - &b__ * i_csc(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_58(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 58,
        source: "UnifyInertTrigFunction[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sec[e_.+f_.*x_])^m_.,x_]",
        pattern: (g__ * i_tan(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, p_, b__, m_],
        when: { freeq!([a__, b__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&g__ * i_cot(&angle)).pow(&p_) * (&a__ + &b__ * i_csc(&angle)).pow(&m_)
        },
    ));
}

fn push_rules_rule_59(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 59,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * i_csc(&angle)).pow(&m_) * (&c__ + &d__ * i_csc(&angle)).pow(&n_)
        },
    ));
}

fn push_rules_rule_60(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 60,
        source: "UnifyInertTrigFunction[(g_.*sec[e_.+f_.*x_])^p_.*(a_.+b_.*sec[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&g__ * &csc).pow(&p_) * (&a__ + &b__ * &csc).pow(&m_) * (&c__ + &d__ * csc).pow(&n_)
        },
    ));
}

fn push_rules_rule_61(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 61,
        source: "UnifyInertTrigFunction[(g_.*cos[e_.+f_.*x_])^p_.*(a_.+b_.*sec[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.,x_]",
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_),
        head: head,
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&g__ * i_sin(&angle)).pow(&p_) * (&a__ + &b__ * &csc).pow(&m_) * (&c__ + &d__ * csc).pow(&n_)
        },
    ));
}

fn push_rules_rule_62(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, capital_a_, capital_b_, m_, n_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 62,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]),x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (d__ * i_sec(e__ + f__ * x_)).pow(n_)
            * (capital_a_ + capital_b_ * i_sec(e__ + f__ * x_)),
        head: head,
        with: [a__, b__, e__, f__, m_, d__, n_, capital_a_, capital_b_, x_],
        optional: [a__, b__, e__, f__, m_, d__, n_, capital_a_, capital_b_],
        when: { freeq!([a__, b__, d__, e__, f__, capital_a_, capital_b_, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_) * (&d__ * &csc).pow(&n_) * (&capital_a_ + &capital_b_ * csc)
        },
    ));
}

fn push_rules_rule_63(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, m_, n_, p_, x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 63,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(c_.+d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_])^p_.,x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_)
            * (capital_a_ + capital_b_ * i_sec(e__ + f__ * x_)).pow(p_),
        head: head,
        with: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_, p_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__, n_, capital_a_, capital_b_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, capital_a_, capital_b_, m_, n_, p_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_)
                * (&c__ + &d__ * &csc).pow(&n_)
                * (&capital_a_ + &capital_b_ * csc).pow(&p_)
        },
    ));
}

fn push_rules_rule_64(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        e__,
        f__,
        capital_a__,
        capital_b__,
        capital_c__,
        m_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 64,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_b__ * i_sec(e__ + f__ * x_) + capital_c__ * i_sec(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        x_dep: [],
        x_free: [a__, b__, e__, f__, m_, capital_a__, capital_b__, capital_c__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_b__, capital_c__, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_)
                * (&capital_a__ + &capital_b__ * &csc + &capital_c__ * csc.pow(2))
        },
    ));
}

fn push_rules_rule_65(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, capital_a__, capital_c__, m_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 65,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (capital_a__ + capital_c__ * i_sec(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, capital_a__, capital_c__],
        x_dep: [],
        x_free: [a__, b__, e__, f__, m_, capital_a__, capital_c__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_c__, m_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_) * (&capital_a__ + &capital_c__ * csc.pow(2))
        },
    ));
}

fn push_rules_rule_66(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        d__,
        e__,
        f__,
        capital_a__,
        capital_b__,
        capital_c__,
        m_,
        n_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 66,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (d__ * i_sec(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_sec(e__ + f__ * x_) + capital_c__ * i_sec(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, d__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, d__, n_, capital_a__, capital_b__, capital_c__],
        x_dep: [],
        x_free: [a__, b__, d__, e__, f__, m_, n_, capital_a__, capital_b__, capital_c__],
        when: { freeq!([a__, b__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_)
                * (&d__ * &csc).pow(&n_)
                * (&capital_a__ + &capital_b__ * &csc + &capital_c__ * csc.pow(2))
        },
    ));
}

fn push_rules_rule_67(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        d__,
        e__,
        f__,
        capital_a__,
        capital_c__,
        m_,
        n_,
        x_
    );
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 67,
        source: "UnifyInertTrigFunction[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(d_.*sec[e_.+f_.*x_])^n_.*(A_.+C_.*sec[e_.+f_.*x_]^2),x_]",
        pattern: (a__ + b__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (d__ * i_sec(e__ + f__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_sec(e__ + f__ * x_).pow(2)),
        head: head,
        with: [a__, b__, e__, f__, m_, d__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, e__, f__, m_, d__, n_, capital_a__, capital_c__],
        x_dep: [],
        x_free: [a__, b__, d__, e__, f__, m_, n_, capital_a__, capital_c__],
        when: { freeq!([a__, b__, d__, e__, f__, capital_a__, capital_c__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            let csc = i_csc(&angle);
            (&a__ + &b__ * &csc).pow(&m_)
                * (&d__ * &csc).pow(&n_)
                * (&capital_a__ + &capital_c__ * csc.pow(2))
        },
    ));
}

fn push_rules_rule_68(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 68,
        source: "UnifyInertTrigFunction[(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_,x_]",
        pattern: (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [a__, b__, c__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_69(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 69,
        source: "UnifyInertTrigFunction[(d_.*cos[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_sin(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_70(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 70,
        source: "UnifyInertTrigFunction[(d_.*sin[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cos(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_71(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 71,
        source: "UnifyInertTrigFunction[(d_.*cot[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_tan(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_72(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 72,
        source: "UnifyInertTrigFunction[(d_.*tan[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_tan(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_cot(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_73(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 73,
        source: "UnifyInertTrigFunction[(d_.*csc[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(n_, 2) && eqq!(p_, 1))
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (-&d__ * i_sec(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_74(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 74,
        source: "UnifyInertTrigFunction[(d_.*sec[e_.+f_.*x_])^m_.*(a_.+b_.*(c_.*csc[e_.+f_.*x_])^n_)^p_.,x_]",
        pattern: (d__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_csc(e__ + f__ * x_)).pow(n_)).pow(p_),
        head: head,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, f__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !(eqq!(a__, 0) && integerq!(p_))
        },
        rhs: {
            let angle = &e__ + Atom::var(Symbol::PI) / 2 + &f__ * x_;
            (&d__ * i_csc(&angle)).pow(&m_)
                * (&a__ + &b__ * (-&c__ * i_sec(&angle)).pow(&n_)).pow(&p_)
        },
    ));
}

fn push_rules_rule_75(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__);
    let head = rubi_symbols().rubi_unify_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 75,
        source: "UnifyInertTrigFunction[u_,x_] := u",
        pattern: Atom::var(u__),
        head: head,
        with: [u__, x_],
        when: { true },
        rhs: { u__ },
    ));
}
