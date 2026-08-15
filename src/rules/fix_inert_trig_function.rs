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
}

fn push_rules_rule_1(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, u__);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 1,
        source: "FixInertTrigFunction[a_*u_,x_]",
        pattern: a__ * u__,
        head: head,
        with: [a__, u__, x_],
        when: { freeq!(a__, x_) },
        rhs: { a__ * rubi_fix_inert_trig_function(&u__, x_) },
    ));
}

fn push_rules_rule_2(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, u__, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    let rule = rubi_helper_row!(
        order: 2,
        source: "FixInertTrigFunction[u_.*(a_*(b_+v_))^n_,x_]",
        pattern: u__ * (a__ * (b__ + Atom::var(v_))).pow(n_),
        head: head,
        with: [u__, a__, b__, v_, n_, x_],
        optional: [u__, n_],
        when: { freeq!([a__, b__, n_], x_) && !freeq!(v_, x_) },
        rhs: { rubi_fix_inert_trig_function(&(u__ * (&a__ * &b__ + &a__ * &v_).pow(&n_)), x_) },
    );
    rules.push(rule.with_early_x_dependent(v_));
}

fn push_rules_rule_3(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 3,
        source: "FixInertTrigFunction[csc[v_]^m_.*(c_.*sin[w_])^n_.,x_]",
        pattern: i_csc(Atom::var(v_)).pow(m_) * (c__ * i_sin(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sin(&v_).pow(-&m_) * (c__ * i_sin(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_4(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 4,
        source: "FixInertTrigFunction[sec[v_]^m_.*(c_.*cos[w_])^n_.,x_]",
        pattern: i_sec(Atom::var(v_)).pow(m_) * (c__ * i_cos(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cos(&v_).pow(-&m_) * (c__ * i_cos(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_5(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 5,
        source: "FixInertTrigFunction[cot[v_]^m_.*(c_.*tan[w_])^n_.,x_]",
        pattern: i_cot(Atom::var(v_)).pow(m_) * (c__ * i_tan(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_tan(&v_).pow(-&m_) * (c__ * i_tan(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_6(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 6,
        source: "FixInertTrigFunction[tan[v_]^m_.*(c_.*cot[w_])^n_.,x_]",
        pattern: i_tan(Atom::var(v_)).pow(m_) * (c__ * i_cot(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cot(&v_).pow(-&m_) * (c__ * i_cot(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_7(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 7,
        source: "FixInertTrigFunction[cos[v_]^m_.*(c_.*sec[w_])^n_.,x_]",
        pattern: i_cos(Atom::var(v_)).pow(m_) * (c__ * i_sec(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sec(&v_).pow(-&m_) * (c__ * i_sec(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_8(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 8,
        source: "FixInertTrigFunction[sin[v_]^m_.*(c_.*csc[w_])^n_.,x_]",
        pattern: i_sin(Atom::var(v_)).pow(m_) * (c__ * i_csc(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_csc(&v_).pow(-&m_) * (c__ * i_csc(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_9(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 9,
        source: "FixInertTrigFunction[sec[v_]^m_.*(c_.*sin[w_])^n_.,x_]",
        pattern: i_sec(Atom::var(v_)).pow(m_) * (c__ * i_sin(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cos(&v_).pow(-&m_) * (c__ * i_sin(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_10(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 10,
        source: "FixInertTrigFunction[csc[v_]^m_.*(c_.*cos[w_])^n_.,x_]",
        pattern: i_csc(Atom::var(v_)).pow(m_) * (c__ * i_cos(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sin(&v_).pow(-&m_) * (c__ * i_cos(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_11(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 11,
        source: "FixInertTrigFunction[cos[v_]^m_.*(c_.*tan[w_])^n_.,x_]",
        pattern: i_cos(Atom::var(v_)).pow(m_) * (c__ * i_tan(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sec(&v_).pow(-&m_) * (c__ * i_tan(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_12(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 12,
        source: "FixInertTrigFunction[sin[v_]^m_.*(c_.*cot[w_])^n_.,x_]",
        pattern: i_sin(Atom::var(v_)).pow(m_) * (c__ * i_cot(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_csc(&v_).pow(-&m_) * (c__ * i_cot(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_13(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 13,
        source: "FixInertTrigFunction[sin[v_]^m_.*(c_.*sec[w_])^n_.,x_]",
        pattern: i_sin(Atom::var(v_)).pow(m_) * (c__ * i_sec(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_csc(&v_).pow(-&m_) * (c__ * i_sec(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_14(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 14,
        source: "FixInertTrigFunction[cos[v_]^m_.*(c_.*csc[w_])^n_.,x_]",
        pattern: i_cos(Atom::var(v_)).pow(m_) * (c__ * i_csc(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sec(&v_).pow(-&m_) * (c__ * i_csc(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_15(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 15,
        source: "FixInertTrigFunction[cot[v_]^m_.*(c_.*sin[w_])^n_.,x_]",
        pattern: i_cot(Atom::var(v_)).pow(m_) * (c__ * i_sin(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_tan(&v_).pow(-&m_) * (c__ * i_sin(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_16(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 16,
        source: "FixInertTrigFunction[tan[v_]^m_.*(c_.*cos[w_])^n_.,x_]",
        pattern: i_tan(Atom::var(v_)).pow(m_) * (c__ * i_cos(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cot(&v_).pow(-&m_) * (c__ * i_cos(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_17(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 17,
        source: "FixInertTrigFunction[csc[v_]^m_.*(c_.*tan[w_])^n_.,x_]",
        pattern: i_csc(Atom::var(v_)).pow(m_) * (c__ * i_tan(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_sin(&v_).pow(-&m_) * (c__ * i_tan(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_18(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 18,
        source: "FixInertTrigFunction[sec[v_]^m_.*(c_.*cot[w_])^n_.,x_]",
        pattern: i_sec(Atom::var(v_)).pow(m_) * (c__ * i_cot(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cos(&v_).pow(-&m_) * (c__ * i_cot(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_19(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 19,
        source: "FixInertTrigFunction[cot[v_]^m_.*(c_.*sec[w_])^n_.,x_]",
        pattern: i_cot(Atom::var(v_)).pow(m_) * (c__ * i_sec(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_tan(&v_).pow(-&m_) * (c__ * i_sec(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_20(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 20,
        source: "FixInertTrigFunction[tan[v_]^m_.*(c_.*csc[w_])^n_.,x_]",
        pattern: i_tan(Atom::var(v_)).pow(m_) * (c__ * i_csc(Atom::var(w_))).pow(n_),
        head: head,
        with: [v_, m_, c__, w_, n_, x_],
        optional: [m_, c__, n_],
        when: { freeq!([c__, n_], x_) && integerq!(m_) },
        rhs: { i_cot(&v_).pow(-&m_) * (c__ * i_csc(&w_)).pow(&n_) },
    ));
}

fn push_rules_rule_21(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 21,
        source: "FixInertTrigFunction[sec[v_]^m_.*sec[w_]^n_.,x_]",
        pattern: i_sec(Atom::var(v_)).pow(m_) * i_sec(Atom::var(w_)).pow(n_),
        head: head,
        with: [v_, m_, w_, n_, x_],
        optional: [m_, n_],
        when: { integerq!(m_) && integerq!(n_) },
        rhs: { i_cos(&v_).pow(-&m_) * i_cos(&w_).pow(-&n_) },
    ));
}

fn push_rules_rule_22(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 22,
        source: "FixInertTrigFunction[csc[v_]^m_.*csc[w_]^n_.,x_]",
        pattern: i_csc(Atom::var(v_)).pow(m_) * i_csc(Atom::var(w_)).pow(n_),
        head: head,
        with: [v_, m_, w_, n_, x_],
        optional: [m_, n_],
        when: { integerq!(m_) && integerq!(n_) },
        rhs: { i_sin(&v_).pow(-&m_) * i_sin(&w_).pow(-&n_) },
    ));
}

fn push_rules_rule_23(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 23,
        source: "FixInertTrigFunction[u_*tan[v_]^m_.*(a_+b_.*sin[w_])^n_.,x_]",
        pattern: u__ * i_tan(Atom::var(v_)).pow(m_) * (a__ + b__ * i_sin(Atom::var(w_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, w_, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) && neq!(b__, 0) && neq!(n_, 0) },
        rhs: {
            i_sin(&v_).pow(&m_) / i_cos(&v_).pow(&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ + b__ * i_sin(&w_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_24(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 24,
        source: "FixInertTrigFunction[u_*cot[v_]^m_.*(a_+b_.*sin[w_])^n_.,x_]",
        pattern: u__ * i_cot(Atom::var(v_)).pow(m_) * (a__ + b__ * i_sin(Atom::var(w_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, w_, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) && neq!(b__, 0) && neq!(n_, 0) },
        rhs: {
            i_cos(&v_).pow(&m_) / i_sin(&v_).pow(&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ + b__ * i_sin(&w_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_25(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 25,
        source: "FixInertTrigFunction[u_*tan[v_]^m_.*(a_+b_.*cos[w_])^n_.,x_]",
        pattern: u__ * i_tan(Atom::var(v_)).pow(m_) * (a__ + b__ * i_cos(Atom::var(w_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, w_, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) && neq!(b__, 0) && neq!(n_, 0) },
        rhs: {
            i_sin(&v_).pow(&m_) / i_cos(&v_).pow(&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ + b__ * i_cos(&w_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_26(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 26,
        source: "FixInertTrigFunction[u_*cot[v_]^m_.*(a_+b_.*cos[w_])^n_.,x_]",
        pattern: u__ * i_cot(Atom::var(v_)).pow(m_) * (a__ + b__ * i_cos(Atom::var(w_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, w_, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) && neq!(b__, 0) && neq!(n_, 0) },
        rhs: {
            i_cos(&v_).pow(&m_) / i_sin(&v_).pow(&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ + b__ * i_cos(&w_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_27(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 27,
        source: "FixInertTrigFunction[cot[v_]^m_.*(a_.+b_.*(c_.*sin[w_])^p_.)^n_.,x_]",
        pattern: i_cot(Atom::var(v_)).pow(m_) * (a__ + b__ * (c__ * i_sin(Atom::var(w_))).pow(p_)).pow(n_),
        head: head,
        with: [v_, m_, a__, b__, c__, w_, p_, n_, x_],
        optional: [m_, a__, b__, c__, p_, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) && integerq!(m_) },
        rhs: { i_tan(&v_).pow(-&m_) * (a__ + b__ * (c__ * i_sin(&w_)).pow(&p_)).pow(&n_) },
    ));
}

fn push_rules_rule_28(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 28,
        source: "FixInertTrigFunction[tan[v_]^m_.*(a_.+b_.*(c_.*cos[w_])^p_.)^n_.,x_]",
        pattern: i_tan(Atom::var(v_)).pow(m_) * (a__ + b__ * (c__ * i_cos(Atom::var(w_))).pow(p_)).pow(n_),
        head: head,
        with: [v_, m_, a__, b__, c__, w_, p_, n_, x_],
        optional: [m_, a__, b__, c__, p_, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) && integerq!(m_) },
        rhs: { i_cot(&v_).pow(-&m_) * (a__ + b__ * (c__ * i_cos(&w_)).pow(&p_)).pow(&n_) },
    ));
}

fn push_rules_rule_29(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 29,
        source: "FixInertTrigFunction[u_.*(c_.*sin[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_sin(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sin, x_) },
        rhs: {
            (c__ * i_sin(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_30(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 30,
        source: "FixInertTrigFunction[u_.*(c_.*cos[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_cos(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cos, x_) },
        rhs: {
            (c__ * i_cos(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_31(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 31,
        source: "FixInertTrigFunction[u_.*(c_.*tan[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_tan(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_tan, x_) },
        rhs: {
            (c__ * i_tan(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_32(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 32,
        source: "FixInertTrigFunction[u_.*(c_.*cot[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_cot(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cot, x_) },
        rhs: {
            (c__ * i_cot(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_33(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 33,
        source: "FixInertTrigFunction[u_.*(c_.*sec[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_sec(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sec, x_) },
        rhs: {
            (c__ * i_sec(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_34(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, p_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 34,
        source: "FixInertTrigFunction[u_.*(c_.*csc[v_]^n_.)^p_.*w_,x_]",
        pattern: u__ * (c__ * i_csc(Atom::var(v_)).pow(n_)).pow(p_) * Atom::var(w_),
        head: head,
        with: [u__, c__, v_, n_, p_, w_, x_],
        optional: [u__, c__, n_, p_],
        when: { freeq!([c__, p_], x_) && rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_csc, x_) },
        rhs: {
            (c__ * i_csc(&v_).pow(&n_)).pow(&p_)
                * rubi_fix_inert_trig_function(&(u__ * w_), x_)
        },
    ));
}

fn push_rules_rule_35(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 35,
        source: "FixInertTrigFunction[u_.*sec[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_3(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cos, x_) && integerq!(n_) },
        rhs: { i_cos(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_36(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 36,
        source: "FixInertTrigFunction[u_.*csc[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_2(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sin, x_) && integerq!(n_) },
        rhs: { i_sin(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_37(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 37,
        source: "FixInertTrigFunction[u_.*sec[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_3(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sin, x_) && integerq!(n_) },
        rhs: { i_cos(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_38(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 38,
        source: "FixInertTrigFunction[u_.*csc[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_2(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cos, x_) && integerq!(n_) },
        rhs: { i_sin(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_39(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 39,
        source: "FixInertTrigFunction[u_.*cot[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_1(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_tan, x_) && integerq!(n_) },
        rhs: { i_tan(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_40(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 40,
        source: "FixInertTrigFunction[u_.*cos[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_0(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_tan, x_) && integerq!(n_) },
        rhs: { i_sec(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_41(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 41,
        source: "FixInertTrigFunction[u_.*cos[v_]^n_*w_,x_]",
        pattern:  rubi_shared_pattern_0(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_tan, x_) && integerq!(n_) },
        rhs: { i_sec(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_42(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 42,
        source: "FixInertTrigFunction[u_.*csc[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_2(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_tan, x_) && integerq!(n_) },
        rhs: { i_sin(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_43(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 43,
        source: "FixInertTrigFunction[u_.*tan[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_5(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cot, x_) && integerq!(n_) },
        rhs: { i_cot(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_44(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 44,
        source: "FixInertTrigFunction[u_.*sin[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_4(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cot, x_) && integerq!(n_) },
        rhs: { i_csc(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_45(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 45,
        source: "FixInertTrigFunction[u_.*sec[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_3(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_cot, x_) && integerq!(n_) },
        rhs: { i_cos(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_46(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 46,
        source: "FixInertTrigFunction[u_.*cos[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_0(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sec, x_) && integerq!(n_) },
        rhs: { i_sec(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_47(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 47,
        source: "FixInertTrigFunction[u_.*cot[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_1(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sec, x_) && integerq!(n_) },
        rhs: { i_tan(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_48(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 48,
        source: "FixInertTrigFunction[u_.*csc[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_2(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_sec, x_) && integerq!(n_) },
        rhs: { i_sin(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_49(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 49,
        source: "FixInertTrigFunction[u_.*sin[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_4(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_csc, x_) && integerq!(n_) },
        rhs: { i_csc(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_50(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 50,
        source: "FixInertTrigFunction[u_.*tan[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_5(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_csc, x_) && integerq!(n_) },
        rhs: { i_cot(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_51(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_, w_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 51,
        source: "FixInertTrigFunction[u_.*sec[v_]^n_.*w_,x_]",
        pattern:  rubi_shared_pattern_3(symbols),
        head: head,
        with: [u__, v_, n_, w_, x_],
        optional: [u__, n_],
        when: { rubi_power_of_inert_trig_sum_q(&w_, rubi_symbols().inert_csc, x_) && integerq!(n_) },
        rhs: { i_cos(&v_).pow(-&n_) * rubi_fix_inert_trig_function(&(u__ * w_), x_) },
    ));
}

fn push_rules_rule_52(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 52,
        source: "FixInertTrigFunction[u_.*tan[v_]^m_.*(a_.*sin[v_]+b_.*cos[v_])^n_.,x_]",
        pattern: u__ * i_tan(Atom::var(v_)).pow(m_) * (a__ * i_sin(Atom::var(v_)) + b__ * i_cos(Atom::var(v_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, n_, x_],
        optional: [u__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) },
        rhs: {
            i_sin(&v_).pow(&m_) * i_cos(&v_).pow(-&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ * i_sin(&v_) + b__ * i_cos(&v_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_53(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 53,
        source: "FixInertTrigFunction[u_.*cot[v_]^m_.*(a_.*sin[v_]+b_.*cos[v_])^n_.,x_]",
        pattern: u__ * i_cot(Atom::var(v_)).pow(m_) * (a__ * i_sin(Atom::var(v_)) + b__ * i_cos(Atom::var(v_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, n_, x_],
        optional: [u__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) },
        rhs: {
            i_cos(&v_).pow(&m_) * i_sin(&v_).pow(-&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ * i_sin(&v_) + b__ * i_cos(&v_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_54(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 54,
        source: "FixInertTrigFunction[u_.*sec[v_]^m_.*(a_.*sin[v_]+b_.*cos[v_])^n_.,x_]",
        pattern: u__ * i_sec(Atom::var(v_)).pow(m_) * (a__ * i_sin(Atom::var(v_)) + b__ * i_cos(Atom::var(v_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, n_, x_],
        optional: [u__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) },
        rhs: {
            i_cos(&v_).pow(-&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ * i_sin(&v_) + b__ * i_cos(&v_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_55(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u__, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 55,
        source: "FixInertTrigFunction[u_.*csc[v_]^m_.*(a_.*sin[v_]+b_.*cos[v_])^n_.,x_]",
        pattern: u__ * i_csc(Atom::var(v_)).pow(m_) * (a__ * i_sin(Atom::var(v_)) + b__ * i_cos(Atom::var(v_))).pow(n_),
        head: head,
        with: [u__, v_, m_, a__, b__, n_, x_],
        optional: [u__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && integerq!(m_) },
        rhs: {
            i_sin(&v_).pow(-&m_)
                * rubi_fix_inert_trig_function(&(u__ * (a__ * i_sin(&v_) + b__ * i_cos(&v_)).pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_56(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_b_, capital_c_, f_, g_, m_, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 56,
        source: "FixInertTrigFunction[f_[v_]^m_.*(A_.+B_.*g_[v_]+C_.*g_[v_]^2),x_]",
        pattern: f_.call( Atom::var(v_)).pow(m_)
            * (capital_a_
                + capital_b_ * g_.call( Atom::var(v_))
                + capital_c_ * g_.call( Atom::var(v_)).pow(2)),
        head: head,
        with: [f_, v_, m_, capital_a_, capital_b_, g_, capital_c_, x_],
        optional: [m_, capital_a_, capital_b_, capital_c_],
        when: {
            freeq!([capital_a_, capital_b_, capital_c_], x_)
                && integerq!(m_)
                && (rubi_inert_reciprocal_q(&f_, &g_) || rubi_inert_reciprocal_q(&g_, &f_))
        },
        rhs: {
            let gv = rubi_function_head_symbol(&g_)?.call( v_);
            gv.pow(-&m_) * (&capital_a_ + &capital_b_ * &gv + &capital_c_ * gv.pow(2))
        },
    ));
}

fn push_rules_rule_57(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_c_, f_, g_, m_, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 57,
        source: "FixInertTrigFunction[f_[v_]^m_.*(A_.+C_.*g_[v_]^2),x_]",
        pattern: f_.call( Atom::var(v_)).pow(m_)
            * (capital_a_ + capital_c_ * g_.call( Atom::var(v_)).pow(2)),
        head: head,
        with: [f_, v_, m_, capital_a_, capital_c_, g_, x_],
        optional: [m_, capital_a_, capital_c_],
        when: {
            freeq!([capital_a_, capital_c_], x_)
                && integerq!(m_)
                && (rubi_inert_reciprocal_q(&f_, &g_) || rubi_inert_reciprocal_q(&g_, &f_))
        },
        rhs: {
            let gv = rubi_function_head_symbol(&g_)?.call( v_);
            gv.pow(-&m_) * (&capital_a_ + &capital_c_ * gv.pow(2))
        },
    ));
}

fn push_rules_rule_58(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a_, capital_b_, capital_c_, a__, b__, f_, g_, m_, n_, v_
    );
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 58,
        source: "FixInertTrigFunction[f_[v_]^m_.*(A_.+B_.*g_[v_]+C_.*g_[v_]^2)*(a_.+b_.*g_[v_])^n_.,x_]",
        pattern: f_.call( Atom::var(v_)).pow(m_)
            * (capital_a_
                + capital_b_ * g_.call( Atom::var(v_))
                + capital_c_ * g_.call( Atom::var(v_)).pow(2))
            * (a__ + b__ * g_.call( Atom::var(v_))).pow(n_),
        head: head,
        with: [f_, v_, m_, capital_a_, capital_b_, g_, capital_c_, a__, b__, n_, x_],
        optional: [m_, capital_a_, capital_b_, capital_c_, a__, b__, n_],
        when: {
            freeq!([a__, b__, capital_a_, capital_b_, capital_c_, n_], x_)
                && integerq!(m_)
                && (rubi_inert_reciprocal_q(&f_, &g_) || rubi_inert_reciprocal_q(&g_, &f_))
        },
        rhs: {
            let gv = rubi_function_head_symbol(&g_)?.call( v_);
            gv.pow(-&m_)
                    * (&capital_a_ + &capital_b_ * &gv + &capital_c_ * gv.pow(2))
                    * (&a__ + &b__ * gv).pow(&n_)
        },
    ));
}

fn push_rules_rule_59(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_c_, a__, b__, f_, g_, m_, n_, v_);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 59,
        source: "FixInertTrigFunction[f_[v_]^m_.*(A_.+C_.*g_[v_]^2)*(a_.+b_.*g_[v_])^n_.,x_]",
        pattern: f_.call( Atom::var(v_)).pow(m_)
            * (capital_a_ + capital_c_ * g_.call( Atom::var(v_)).pow(2))
            * (a__ + b__ * g_.call( Atom::var(v_))).pow(n_),
        head: head,
        with: [f_, v_, m_, capital_a_, capital_c_, g_, a__, b__, n_, x_],
        optional: [m_, capital_a_, capital_c_, a__, b__, n_],
        when: {
            freeq!([a__, b__, capital_a_, capital_c_, n_], x_)
                && integerq!(m_)
                && (rubi_inert_reciprocal_q(&f_, &g_) || rubi_inert_reciprocal_q(&g_, &f_))
        },
        rhs: {
            let gv = rubi_function_head_symbol(&g_)?.call( v_);
            gv.pow(-&m_)
                    * (&capital_a_ + &capital_c_ * gv.pow(2))
                    * (&a__ + &b__ * gv).pow(&n_)
        },
    ));
}

fn push_rules_rule_60(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__);
    let head = rubi_symbols().rubi_fix_inert_trig_function;
    rules.push(rubi_helper_row!(
        order: 60,
        source: "FixInertTrigFunction[u_,x_] := u",
        pattern: Atom::var(u__),
        head: head,
        with: [u__, x_],
        when: { true },
        rhs: { u__ },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_cos(Atom::var(v_)).pow(n_) * Atom::var(w_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_cot(Atom::var(v_)).pow(n_) * Atom::var(w_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_csc(Atom::var(v_)).pow(n_) * Atom::var(w_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_sec(Atom::var(v_)).pow(n_) * Atom::var(w_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_sin(Atom::var(v_)).pow(n_) * Atom::var(w_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * i_tan(Atom::var(v_)).pow(n_) * Atom::var(w_)
}
