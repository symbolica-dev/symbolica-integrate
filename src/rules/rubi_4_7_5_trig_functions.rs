use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4820(rules);
    push_rules_rule_4821(rules);
    push_rules_rule_4822(rules);
    push_rules_rule_4823(rules);
    push_rules_rule_4824(rules);
    push_rules_rule_4825(rules);
    push_rules_rule_4826(rules);
    push_rules_rule_4827(rules);
    push_rules_rule_4828(rules);
    push_rules_rule_4829(rules);
    push_rules_rule_4830(rules);
    push_rules_rule_4831(rules);
    push_rules_rule_4832(rules);
    push_rules_rule_4833(rules);
    push_rules_rule_4834(rules);
    push_rules_rule_4835(rules);
    push_rules_rule_4836(rules);
    push_rules_rule_4837(rules);
    push_rules_rule_4838(rules);
    push_rules_rule_4839(rules);
    push_rules_rule_4840(rules);
    push_rules_rule_4841(rules);
    push_rules_rule_4842(rules);
    push_rules_rule_4843(rules);
    push_rules_rule_4844(rules);
    push_rules_rule_4845(rules);
    push_rules_rule_4846(rules);
    push_rules_rule_4847(rules);
    push_rules_rule_4848(rules);
    push_rules_rule_4849(rules);
    push_rules_rule_4850(rules);
    push_rules_rule_4851(rules);
    push_rules_rule_4852(rules);
    push_rules_rule_4853(rules);
    push_rules_rule_4854(rules);
    push_rules_rule_4855(rules);
    push_rules_rule_4856(rules);
    push_rules_rule_4857(rules);
    push_rules_rule_4858(rules);
    push_rules_rule_4859(rules);
    push_rules_rule_4860(rules);
    push_rules_rule_4861(rules);
    push_rules_rule_4862(rules);
    push_rules_rule_4863(rules);
    push_rules_rule_4864(rules);
    push_rules_rule_4865(rules);
    push_rules_rule_4866(rules);
    push_rules_rule_4867(rules);
    push_rules_rule_4868(rules);
    push_rules_rule_4869(rules);
    push_rules_rule_4870(rules);
    push_rules_rule_4871(rules);
    push_rules_rule_4872(rules);
    push_rules_rule_4873(rules);
    push_rules_rule_4874(rules);
    push_rules_rule_4875(rules);
    push_rules_rule_4876(rules);
    push_rules_rule_4877(rules);
    push_rules_rule_4878(rules);
    push_rules_rule_4879(rules);
    push_rules_rule_4880(rules);
    push_rules_rule_4881(rules);
    push_rules_rule_4882(rules);
    push_rules_rule_4883(rules);
    push_rules_rule_4884(rules);
    push_rules_rule_4885(rules);
    push_rules_rule_4886(rules);
    push_rules_rule_4887(rules);
    push_rules_rule_4888(rules);
    push_rules_rule_4889(rules);
    push_rules_rule_4890(rules);
    push_rules_rule_4891(rules);
    push_rules_rule_4892(rules);
    push_rules_rule_4893(rules);
    push_rules_rule_4894(rules);
    push_rules_rule_4895(rules);
    push_rules_rule_4896(rules);
    push_rules_rule_4897(rules);
    push_rules_rule_4898(rules);
    push_rules_rule_4899(rules);
    push_rules_rule_4900(rules);
    push_rules_rule_4901(rules);
    push_rules_rule_4902(rules);
    push_rules_rule_4903(rules);
}

fn push_rules_rule_4820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4820,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*sin[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[m*ArcTan[x]]+b*Sin[n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m/2] && IntegerQ[n/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.atan()).sin() + &b__ * (&n_ * z.atan()).sin();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4821,
        source: "Int[(a_.*cos[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Cos[m*ArcCot[x]]+b*Cos[n*ArcCot[x]]]]^p/(1+x^2),x],x,Cot[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m/2] && IntegerQ[n/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.acot()).cos() + &b__ * (&n_ * z.acot()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).cot();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4822,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*sin[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[m*ArcTan[x]]+b*Sin[n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p/2,0] && IntegerQ[(m-1)/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(&p_ / 2, 0)
                && integerq!((&m_ - 1) / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.atan()).sin() + &b__ * (&n_ * z.atan()).sin();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4823,
        source: "Int[(a_.*cos[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Cos[m*ArcTan[x]]+b*Cos[n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p/2,0] && IntegerQ[(m-1)/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(&p_ / 2, 0)
                && integerq!((&m_ - 1) / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.atan()).cos() + &b__ * (&n_ * z.atan()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4824,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*sin[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[m*ArcCos[x]]+b*Sin[n*ArcCos[x]]]]^p/Sqrt[1-x^2],x],x,Cos[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[(p-1)/2,0] && IntegerQ[(m-1)/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!((&p_ - 1) / 2, 0)
                && integerq!((&m_ - 1) / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.acos()).sin() + &b__ * (&n_ * z.acos()).sin();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) - z.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).cos();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4825,
        source: "Int[(a_.*cos[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Cos[m*ArcSin[x]]+b*Cos[n*ArcSin[x]]]]^p/Sqrt[1-x^2],x],x,Sin[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[(p-1)/2,0] && IntegerQ[(m-1)/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!((&p_ - 1) / 2, 0)
                && integerq!((&m_ - 1) / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.asin()).cos() + &b__ * (&n_ * z.asin()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) - z.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).sin();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4826,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*sin[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          2/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[2*m*ArcTan[x]]+b*Sin[2*n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[1/2*(c+d*x)]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(&m_ / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (Atom::num(2) * &m_ * z.atan()).sin()
                + &b__ * (Atom::num(2) * &n_ * z.atan()).sin();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = ((&c__ + &d__ * x_) / 2).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4827,
        source: "Int[(a_.*cos[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          -2/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Cos[2*m*ArcCot[x]]+b*Cos[2*n*ArcCot[x]]]]^p/(1+x^2),x],x,Cot[1/2*(c+d*x)]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(&m_ / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (Atom::num(2) * &m_ * z.acot()).cos()
                + &b__ * (Atom::num(2) * &n_ * z.acot()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = ((&c__ + &d__ * x_) / 2).cot();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(-Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4828,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[m*ArcTan[x]]+b*Cos[n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m/2] && IntegerQ[n/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.atan()).sin() + &b__ * (&n_ * z.atan()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4829,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          1/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[m*ArcSin[x]]+b*Cos[n*ArcSin[x]]]]^p/Sqrt[1-x^2],x],x,Sin[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[(p-1)/2,0] && IntegerQ[m/2] && IntegerQ[(n-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!((&p_ - 1) / 2, 0)
                && integerq!(&m_ / 2)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (&m_ * z.asin()).sin() + &b__ * (&n_ * z.asin()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) - z.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = (&c__ + &d__ * x_).sin();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4830,
        source: "Int[(a_.*sin[m_.*(c_.+d_.*x_)]+b_.*cos[n_.*(c_.+d_.*x_)])^p_,x_Symbol] :=
          2/d \\[Star] Subst[Int[Simplify[TrigExpand[a*Sin[2*m*ArcTan[x]]+b*Cos[2*n*ArcTan[x]]]]^p/(1+x^2),x],x,Tan[1/2*(c+d*x)]] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m] && IntegerQ[n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(m_)
                && integerq!(n_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let inner = &a__ * (Atom::num(2) * &m_ * z.atan()).sin()
                + &b__ * (Atom::num(2) * &n_ * z.atan()).cos();
            let expanded = rubi_normalize_inverse_trig_trig(&inner);
            let integrand = rubi_simplify(&expanded).pow(&p_) / (Atom::num(1) + z.pow(2));
            let recursive = rubi_rhs_int(&integrand, sub);
            let replacement = ((&c__ + &d__ * x_) / 2).tan();
            let substituted = rubi_subst(&recursive, sub, replacement);
            rubi_star(Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_4831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_, v_);
    rules.push(rubi_rule!(
        order: 4831,
        source: "Int[(a_.*sin[u_]+b_.*sin[v_])^p_,x_Symbol] :=
          With[{m=Denominator[f/d]},
          Int[(a*Sin[m*(c/m+d*x/m)]+b*Sin[m*f/d*(c/m+d*x/m)])^p,x]] /;
        FreeQ[{a,b},x] && LinearQ[{u,v},x] && ILtQ[p,0] && EqQ[d*e-c*f,0] && RationalQ[f/d]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * i_sin(Atom::var(u_)) + b__ * i_sin(Atom::var(v_))).pow(p_),
        with: [a__, b__, u_, v_, p_, x_],
        optional: [a__, b__],
        when: {
            let c = Atom::var(symbol!("c"));
            let d = Atom::var(symbol!("d"));
            let e = Atom::var(symbol!("e"));
            let f = Atom::var(symbol!("f"));
            freeq!([a__, b__], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && iltq!(p_, 0)
                && eqq!(&d * &e - &c * &f, 0)
                && rational_q(&(&f / &d))
        },
        rhs: {
            let c = Atom::var(symbol!("c"));
            let d = Atom::var(symbol!("d"));
            let f = Atom::var(symbol!("f"));
            let m = rubi_denominator_atom(&(&f / &d));
            let base = &c / &m + &d * (x_ / &m);
            let integrand = (&a__ * (&m * &base).sin()
                + &b__ * (&m * (&f / &d) * &base).sin())
                .pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4832,
        source: "Int[(a_.*F_[c_.+d_.*x_]^p_)^n_,x_Symbol] :=
          With[{v=ActivateTrig[F[c+d*x]]},
          a^IntPart[n]*(v/NonfreeFactors[v,x])^(p*IntPart[n])*(a*v^p)^FracPart[n]/NonfreeFactors[v,x]^(p*FracPart[n]) \\[Star]
            Int[NonfreeFactors[v,x]^(n*p),x]] /;
        FreeQ[{a,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && IntegerQ[p]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * capital_f_.call( c__ + d__ * x_).pow(p_)).pow(n_),
        with: [a__, capital_f_, c__, d__, p_, n_, x_],
        optional: [a__, c__, d__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && rubi_inert_trig_q(&capital_f_)
                && !integerq!(n_)
                && integerq!(p_)
        },
        rhs: {
            let v = rubi_activate_trig(&rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &c__ + &d__ * x_));
            let nonfree_factors = rubi_nonfree_factors(&v, x_);
            let int_n = rubi_int_part(&n_);
            let frac_n = rubi_frac_part(&n_);
            let recursive = rubi_rhs_int(&nonfree_factors.pow(&n_ * &p_), x_);
            let coefficient = a__.pow(&int_n)
                * (&v / &nonfree_factors).pow(&p_ * &int_n)
                * (&a__ * v.pow(&p_)).pow(&frac_n)
                / nonfree_factors.pow(&p_ * &frac_n);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4833,
        source: "Int[(a_.*(b_.*F_[c_.+d_.*x_])^p_)^n_.,x_Symbol] :=
          With[{v=ActivateTrig[F[c+d*x]]},
          a^IntPart[n]*(a*(b*v)^p)^FracPart[n]/(b*v)^(p*FracPart[n]) \\[Star] Int[(b*v)^(n*p),x]] /;
        FreeQ[{a,b,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * (b__ * capital_f_.call( c__ + d__ * x_)).pow(p_)).pow(n_),
        with: [a__, b__, capital_f_, c__, d__, p_, n_, x_],
        optional: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_inert_trig_q(&capital_f_)
                && !integerq!(n_)
                && !integerq!(p_)
        },
        rhs: {
            let v = rubi_activate_trig(&rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &c__ + &d__ * x_));
            let frac_n = rubi_frac_part(&n_);
            let recursive = rubi_rhs_int(&((&b__ * &v).pow(&n_ * &p_)), x_);
            let coefficient = a__.pow(rubi_int_part(&n_))
                * (&a__ * (&b__ * &v).pow(&p_)).pow(&frac_n)
                / (&b__ * &v).pow(&p_ * &frac_n);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4834,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Cos] || EqQ[F,cos])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_pure_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(&ff / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4835,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Sin] || EqQ[F,sin])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_pure_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-&ff / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4836,
        source: "Int[u_*Cosh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_pure_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(&ff / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4837,
        source: "Int[u_*Sinh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_pure_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(&ff / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4838,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Cot] || EqQ[F,cot])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::cot(), rubi_symbols().inert_cot]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_pure_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4839,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Tan] || EqQ[F,tan])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::tan(), rubi_symbols().inert_tan]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_pure_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4840,
        source: "Int[u_*Coth[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_pure_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4841,
        source: "Int[u_*Tanh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_pure_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4842,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
         FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u] && (EqQ[F,Sec] || EqQ[F,sec])",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::sec(), rubi_symbols().inert_sec]))
                && {
                    let tan = (&c__ * (&a__ + &b__ * x_)).tan();
                    let ff = rubi_free_factors(&tan, x_);
                    rubi_pure_function_of_q(&(tan / ff), &u__, x_)
                }
        },
        rhs: {
            let tan = (&c__ * (&a__ + &b__ * x_)).tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = tan / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(&ff / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4843,
        source: "Int[u_/cos[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
         FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern: u__ / i_cos(c__ * (a__ + b__ * x_)).pow(2),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && {
                    let tan = (&c__ * (&a__ + &b__ * x_)).tan();
                    let ff = rubi_free_factors(&tan, x_);
                    rubi_pure_function_of_q(&(tan / ff), &u__, x_)
                }
        },
        rhs: {
            let tan = (&c__ * (&a__ + &b__ * x_)).tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = tan / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4844,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
         FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u] && (EqQ[F,Csc] || EqQ[F,csc])",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::csc(), rubi_symbols().inert_csc]))
                && {
                    let cot = (&c__ * (&a__ + &b__ * x_)).cot();
                    let ff = rubi_free_factors(&cot, x_);
                    rubi_pure_function_of_q(&(cot / ff), &u__, x_)
                }
        },
        rhs: {
            let cot = (&c__ * (&a__ + &b__ * x_)).cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = cot / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4845,
        source: "Int[u_/sin[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
         FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern: u__ / i_sin(c__ * (a__ + b__ * x_)).pow(2),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && {
                    let cot = (&c__ * (&a__ + &b__ * x_)).cot();
                    let ff = rubi_free_factors(&cot, x_);
                    rubi_pure_function_of_q(&(cot / ff), &u__, x_)
                }
        },
        rhs: {
            let cot = (&c__ * (&a__ + &b__ * x_)).cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = cot / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4846,
        source: "Int[u_*Sech[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Tanh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Tanh[c*(a+b*x)]/d,u,x],x],x,Tanh[c*(a+b*x)]/d] /;
         FunctionOfQ[Tanh[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).sech().pow(2),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && {
                    let tanh = (&c__ * (&a__ + &b__ * x_)).tanh();
                    let ff = rubi_free_factors(&tanh, x_);
                    rubi_pure_function_of_q(&(tanh / ff), &u__, x_)
                }
        },
        rhs: {
            let tanh = (&c__ * (&a__ + &b__ * x_)).tanh();
            let ff = rubi_free_factors(&tanh, x_);
            let base = tanh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4847,
        source: "Int[u_*Csch[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
          With[{d=FreeFactors[Coth[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[1,Coth[c*(a+b*x)]/d,u,x],x],x,Coth[c*(a+b*x)]/d] /;
         FunctionOfQ[Coth[c*(a+b*x)]/d,u,x,True]] /;
        FreeQ[{a,b,c},x] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).csch().pow(2),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nonsum_q(&u__)
                && {
                    let coth = (&c__ * (&a__ + &b__ * x_)).coth();
                    let ff = rubi_free_factors(&coth, x_);
                    rubi_pure_function_of_q(&(coth / ff), &u__, x_)
                }
        },
        rhs: {
            let coth = (&c__ * (&a__ + &b__ * x_)).coth();
            let ff = rubi_free_factors(&coth, x_);
            let base = coth / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4848,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
          With[{d=FreeFactors[Tan[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Tan[c*(a+b*x)]/d,u,x],x],x,Tan[c*(a+b*x)]/d] /;
         FunctionOfQ[Tan[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Cot[c*(a+b*x)]^n,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && (EqQ[F,Cot] || EqQ[F,cot])",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::cot(), rubi_symbols().inert_cot]))
                && {
                    let angle = &c__ * (&a__ + &b__ * x_);
                    let tan = angle.tan();
                    let ff = rubi_free_factors(&tan, x_);
                    let activated = rubi_activate_trig(&u__) * angle.cot().pow(&n_);
                    rubi_pure_function_of_q(&(tan / ff), &u__, x_)
                        && rubi_try_pure_tan_subst(&activated, x_)
                }
        },
        rhs: {
            let tan = (&c__ * (&a__ + &b__ * x_)).tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = tan / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol)
                / (sub.pow(&n_) * (Atom::num(1) + ff.pow(2) * sub.pow(2)));
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4849,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
          With[{d=FreeFactors[Cot[c*(a+b*x)],x]},
          -1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[1/(x^n*(1+d^2*x^2)),Cot[c*(a+b*x)]/d,u,x],x],x,Cot[c*(a+b*x)]/d] /;
         FunctionOfQ[Cot[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Tan[c*(a+b*x)]^n,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && (EqQ[F,Tan] || EqQ[F,tan])",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::tan(), rubi_symbols().inert_tan]))
                && {
                    let angle = &c__ * (&a__ + &b__ * x_);
                    let cot = angle.cot();
                    let ff = rubi_free_factors(&cot, x_);
                    let activated = rubi_activate_trig(&u__) * angle.tan().pow(&n_);
                    rubi_pure_function_of_q(&(cot / ff), &u__, x_)
                        && rubi_try_pure_tan_subst(&activated, x_)
                }
        },
        rhs: {
            let cot = (&c__ * (&a__ + &b__ * x_)).cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = cot / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol)
                / (sub.pow(&n_) * (Atom::num(1) + ff.pow(2) * sub.pow(2)));
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4850,
        source: "Int[u_*Coth[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
          With[{d=FreeFactors[Tanh[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[1/(x^n*(1-d^2*x^2)),Tanh[c*(a+b*x)]/d,u,x],x],x,Tanh[c*(a+b*x)]/d] /;
         FunctionOfQ[Tanh[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Coth[c*(a+b*x)]^n,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && {
                    let angle = &c__ * (&a__ + &b__ * x_);
                    let tanh = angle.tanh();
                    let ff = rubi_free_factors(&tanh, x_);
                    let activated = rubi_activate_trig(&u__) * angle.coth().pow(&n_);
                    rubi_pure_function_of_q(&(tanh / ff), &u__, x_)
                        && rubi_try_pure_tan_subst(&activated, x_)
                }
        },
        rhs: {
            let tanh = (&c__ * (&a__ + &b__ * x_)).tanh();
            let ff = rubi_free_factors(&tanh, x_);
            let base = tanh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol)
                / (sub.pow(&n_) * (Atom::num(1) - ff.pow(2) * sub.pow(2)));
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4851,
        source: "Int[u_*Tanh[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
          With[{d=FreeFactors[Coth[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[1/(x^n*(1-d^2*x^2)),Coth[c*(a+b*x)]/d,u,x],x],x,Coth[c*(a+b*x)]/d] /;
         FunctionOfQ[Coth[c*(a+b*x)]/d,u,x,True] && TryPureTanSubst[ActivateTrig[u]*Tanh[c*(a+b*x)]^n,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n]",
        desc: "Integration by substitution",
        refs: ["G&R 2.504"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && {
                    let angle = &c__ * (&a__ + &b__ * x_);
                    let coth = angle.coth();
                    let ff = rubi_free_factors(&coth, x_);
                    let activated = rubi_activate_trig(&u__) * angle.tanh().pow(&n_);
                    rubi_pure_function_of_q(&(coth / ff), &u__, x_)
                        && rubi_try_pure_tan_subst(&activated, x_)
                }
        },
        rhs: {
            let coth = (&c__ * (&a__ + &b__ * x_)).coth();
            let ff = rubi_free_factors(&coth, x_);
            let base = coth / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol)
                / (sub.pow(&n_) * (Atom::num(1) - ff.pow(2) * sub.pow(2)));
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_);
    rules.push(rubi_rule!(
        order: 4852,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfTrig[u,x]},
          With[{d=FreeFactors[Cot[v],x]},
          -d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1/(1+d^2*x^2),Cot[v]/d,u,x],x],x,Cot[v]/d]] /;
         Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cot[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u_, x_],
        when: {
            rubi_function_of_trig(&u_, x_).is_some_and(|v| {
                let cot = rubi_activate_trig(&v.cot());
                rubi_pure_function_of_q(&rubi_nonfree_factors(&cot, x_), &u_, x_)
                    && rubi_try_pure_tan_subst(&rubi_activate_trig(&u_), x_)
            })
        },
        rhs: {
            let v = rubi_function_of_trig(&u_, x_).rubi_rhs();
            let cot = rubi_activate_trig(&v.cot());
            let ff = rubi_free_factors(&cot, x_);
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let base = cot / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let substitution_factor =
                Atom::num(1) / (Atom::num(1) + ff.pow(2) * sub.pow(2));
            let transformed_integrand =
                rubi_subst_for_factor(&substitution_factor, &base, &u_, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_);
    rules.push(rubi_rule!(
        order: 4853,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfTrig[u,x]},
          With[{d=FreeFactors[Tan[v],x]},
          d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d]] /;
         Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x,True] && TryPureTanSubst[ActivateTrig[u],x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u_, x_],
        when: {
            rubi_function_of_trig(&u_, x_).is_some_and(|v| {
                let tan = rubi_activate_trig(&v.tan());
                rubi_pure_function_of_q(&rubi_nonfree_factors(&tan, x_), &u_, x_)
                    && rubi_try_pure_tan_subst(&rubi_activate_trig(&u_), x_)
            })
        },
        rhs: {
            let v = rubi_function_of_trig(&u_, x_).rubi_rhs();
            let tan = rubi_activate_trig(&v.tan());
            let ff = rubi_free_factors(&tan, x_);
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let base = tan / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let substitution_factor =
                Atom::num(1) / (Atom::num(1) + ff.pow(2) * sub.pow(2));
            let transformed_integrand =
                rubi_subst_for_factor(&substitution_factor, &base, &u_, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 4854,
        source: "Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q],x],x] /;
        FreeQ[{a,b,c,d},x] && (EqQ[F,sin] || EqQ[F,cos]) && (EqQ[G,sin] || EqQ[G,cos]) && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.call( a__ + b__ * x_).pow(p_)
            * capital_g_.call( c__ + d__ * x_).pow(q_),
        with: [capital_f_, a__, b__, p_, capital_g_, c__, d__, q_, x_],
        optional: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]) || rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && (rubi_function_head_member_q(&capital_g_, &[Symbol::SIN, rubi_symbols().inert_sin]) || rubi_function_head_member_q(&capital_g_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &a__ + &b__ * x_).pow(&p_)
                * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &c__ + &d__ * x_).pow(&q_);
            let expanded = rubi_expand_trig_reduce_one(&rubi_activate_trig(&integrand), x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 4855,
        source: "Int[F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.*H_[e_.+f_.*x_]^r_.,x_Symbol] :=
          Int[ExpandTrigReduce[ActivateTrig[F[a+b*x]^p*G[c+d*x]^q*H[e+f*x]^r],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && (EqQ[F,sin] || EqQ[F,cos]) && (EqQ[G,sin] || EqQ[G,cos]) && (EqQ[H,sin] || EqQ[H,cos]) && IGtQ[p,0] && IGtQ[q,0] && IGtQ[r,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.call( a__ + b__ * x_).pow(p_)
            * capital_g_.call( c__ + d__ * x_).pow(q_)
            * capital_h_.call( e__ + f__ * x_).pow(r_),
        with: [capital_f_, a__, b__, p_, capital_g_, c__, d__, q_, capital_h_, e__, f__, r_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]) || rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && (rubi_function_head_member_q(&capital_g_, &[Symbol::SIN, rubi_symbols().inert_sin]) || rubi_function_head_member_q(&capital_g_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && (rubi_function_head_member_q(&capital_h_, &[Symbol::SIN, rubi_symbols().inert_sin]) || rubi_function_head_member_q(&capital_h_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let integrand = rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &a__ + &b__ * x_).pow(&p_)
                * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &c__ + &d__ * x_).pow(&q_)
                * rubi_function_head_symbol(&capital_h_).rubi_rhs().call( &e__ + &f__ * x_).pow(&r_);
            let expanded = rubi_expand_trig_reduce_one(&rubi_activate_trig(&integrand), x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4856,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Cos] || EqQ[F,cos])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4857,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Sin] || EqQ[F,sin])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4858,
        source: "Int[u_*Cosh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4859,
        source: "Int[u_*Sinh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[1,Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4860,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Cot] || EqQ[F,cot])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::cot(), rubi_symbols().inert_cot]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4861,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && (EqQ[F,Tan] || EqQ[F,tan])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, capital_f_, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::tan(), rubi_symbols().inert_tan]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4862,
        source: "Int[u_*Coth[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 4863,
        source: "Int[u_*Tanh[c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          1/(b*c) \\[Star] Subst[Int[SubstFor[1/x,Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = rubi_subst_for(&u__, &base, substitution_symbol) / &sub;
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4864,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Cos] || EqQ[F,cos])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4865,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Sec] || EqQ[F,sec])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::sec(), rubi_symbols().inert_sec]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((-&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4866,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Sin] || EqQ[F,sin])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4867,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -d/(b*c) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((-n-1)/2),Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Csc] || EqQ[F,csc])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::csc(), rubi_symbols().inert_csc]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((-&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4868,
        source: "Int[u_*Cosh[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(1+d^2*x^2)^((n-1)/2),Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).cosh().pow(n_),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4869,
        source: "Int[u_*Sech[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(1+d^2*x^2)^((-n-1)/2),Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).sech().pow(n_),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((-&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4870,
        source: "Int[u_*Sinh[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(-1+d^2*x^2)^((n-1)/2),Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).sinh().pow(n_),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (-Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4871,
        source: "Int[u_*Csch[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          d/(b*c) \\[Star] Subst[Int[SubstFor[(-1+d^2*x^2)^((-n-1)/2),Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern: u__ * (c__ * (a__ + b__ * x_)).csch().pow(n_),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (-Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((-&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff * Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_4872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4872,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sin[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Sin[c*(a+b*x)]/d,u,x],x],x,Sin[c*(a+b*x)]/d] /;
         FunctionOfQ[Sin[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Cot] || EqQ[F,cot])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::cot(), rubi_symbols().inert_cot]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let sin = (&c__ * (&a__ + &b__ * x_)).sin();
            let ff = rubi_free_factors(&sin, x_);
            let base = sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol)
                / sub.pow(&n_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4873,
        source: "Int[u_*F_[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cos[c*(a+b*x)],x]},
          -1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[(1-d^2*x^2)^((n-1)/2)/x^n,Cos[c*(a+b*x)]/d,u,x],x],x,Cos[c*(a+b*x)]/d] /;
         FunctionOfQ[Cos[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Tan] || EqQ[F,tan])",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [u__, capital_f_, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[symbolica::transcendental::tan(), rubi_symbols().inert_tan]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let cos = (&c__ * (&a__ + &b__ * x_)).cos();
            let ff = rubi_free_factors(&cos, x_);
            let base = cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) - ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol)
                / sub.pow(&n_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4874,
        source: "Int[u_*Coth[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Sinh[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[(1+d^2*x^2)^((n-1)/2)/x^n,Sinh[c*(a+b*x)]/d,u,x],x],x,Sinh[c*(a+b*x)]/d] /;
         FunctionOfQ[Sinh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
                    let ff = rubi_free_factors(&sinh, x_);
                    rubi_function_of_q(&(sinh / ff), &u__, x_)
                }
        },
        rhs: {
            let sinh = (&c__ * (&a__ + &b__ * x_)).sinh();
            let ff = rubi_free_factors(&sinh, x_);
            let base = sinh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol)
                / sub.pow(&n_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4875,
        source: "Int[u_*Tanh[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
          With[{d=FreeFactors[Cosh[c*(a+b*x)],x]},
          1/(b*c*d^(n-1)) \\[Star] Subst[Int[SubstFor[(-1+d^2*x^2)^((n-1)/2)/x^n,Cosh[c*(a+b*x)]/d,u,x],x],x,Cosh[c*(a+b*x)]/d] /;
         FunctionOfQ[Cosh[c*(a+b*x)]/d,u,x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[(n-1)/2] && NonsumQ[u]",
        desc: "Integration by substitution",
        refs: ["G&R 2.503, CRC 483", "G&R 2.502, CRC 482"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && {
                    let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
                    let ff = rubi_free_factors(&cosh, x_);
                    rubi_function_of_q(&(cosh / ff), &u__, x_)
                }
        },
        rhs: {
            let cosh = (&c__ * (&a__ + &b__ * x_)).cosh();
            let ff = rubi_free_factors(&cosh, x_);
            let base = cosh / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (-Atom::num(1) + ff.pow(2) * sub.pow(2)).pow((&n_ - 1) / 2)
                * rubi_subst_for(&u__, &base, substitution_symbol)
                / sub.pow(&n_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(1) / (&b__ * &c__ * ff.pow(&n_ - 1)), substituted)
        },
    ));
}

fn push_rules_rule_4876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, u__, v_, x_);
    let rule = rubi_rule!(
        order: 4876,
        source: "Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
          With[{e=FreeFactors[Sin[c*(a+b*x)],x]},
          Int[ActivateTrig[u*v],x] + d \\[Star] Int[ActivateTrig[u]*Cos[c*(a+b*x)]^n,x] /;
         FunctionOfQ[Sin[c*(a+b*x)]/e,u,x]] /;
        FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Cos] || EqQ[F,cos])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, v_, d__, capital_f_, c__, a__, b__, n_, x_],
        optional: [d__, c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && !freeq!(v_, x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && {
                    let sin = (&c__ * (&a__ + &b__ * x_)).sin();
                    let ff = rubi_free_factors(&sin, x_);
                    rubi_function_of_q(&(sin / ff), &u__, x_)
                }
        },
        rhs: {
            let first = rubi_rhs_int(&rubi_activate_trig(&(&u__ * &v_)), x_);
            let second_integrand =
                rubi_activate_trig(&u__) * (&c__ * (&a__ + &b__ * x_)).cos().pow(&n_);
            let second = rubi_rhs_int(&second_integrand, x_);

            first + rubi_star(d__, second)
        },
    );
    rules.push(rule.with_early_x_dependent(v_));
}

fn push_rules_rule_4877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, u__, v_, x_);
    let rule = rubi_rule!(
        order: 4877,
        source: "Int[u_*(v_+d_.*F_[c_.*(a_.+b_.*x_)]^n_.),x_Symbol] :=
          With[{e=FreeFactors[Cos[c*(a+b*x)],x]},
          Int[ActivateTrig[u*v],x] + d \\[Star] Int[ActivateTrig[u]*Sin[c*(a+b*x)]^n,x] /;
         FunctionOfQ[Cos[c*(a+b*x)]/e,u,x]] /;
        FreeQ[{a,b,c,d},x] && Not[FreeQ[v,x]] && IntegerQ[(n-1)/2] && NonsumQ[u] && (EqQ[F,Sin] || EqQ[F,sin])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, v_, d__, capital_f_, c__, a__, b__, n_, x_],
        optional: [d__, c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && !freeq!(v_, x_)
                && integerq!((&n_ - 1) / 2)
                && rubi_nonsum_q(&u__)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin]))
                && {
                    let cos = (&c__ * (&a__ + &b__ * x_)).cos();
                    let ff = rubi_free_factors(&cos, x_);
                    rubi_function_of_q(&(cos / ff), &u__, x_)
                }
        },
        rhs: {
            let first = rubi_rhs_int(&rubi_activate_trig(&(&u__ * &v_)), x_);
            let second_integrand =
                rubi_activate_trig(&u__) * (&c__ * (&a__ + &b__ * x_)).sin().pow(&n_);
            let second = rubi_rhs_int(&second_integrand, x_);

            first + rubi_star(d__, second)
        },
    );
    rules.push(rule.with_early_x_dependent(v_));
}

fn push_rules_rule_4878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_);
    rules.push(rubi_rule!(
        order: 4878,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfTrig[u,x]},
          With[{d=FreeFactors[Sin[v],x]},
          d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1,Sin[v]/d,u/Cos[v],x],x],x,Sin[v]/d]] /;
         Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Sin[v],x],u/Cos[v],x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u_, x_],
        when: {
            rubi_function_of_trig(&u_, x_).is_some_and(|v| {
                // Mathematica evaluates Sin[I*z] and Cos[I*z] to their
                // hyperbolic forms before NonfreeFactors and FunctionOfQ.
                let sin = rubi_mathematica_evaluate_active_trig_call(Symbol::SIN, v.to_owned());
                let cos = rubi_mathematica_evaluate_active_trig_call(Symbol::COS, v);
                let payload = &u_ / cos;
                rubi_function_of_q(&rubi_nonfree_factors(&sin, x_), &payload, x_)
            })
        },
        rhs: {
            let v = rubi_function_of_trig(&u_, x_).rubi_rhs();
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let sin = rubi_mathematica_evaluate_active_trig_call(Symbol::SIN, v.to_owned());
            let cos = rubi_mathematica_evaluate_active_trig_call(Symbol::COS, v);
            let ff = rubi_free_factors(&sin, x_);
            let base = &sin / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for_factor(
                &Atom::num(1),
                &base,
                &(&u_ / cos),
                substitution_symbol,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_);
    rules.push(rubi_rule!(
        order: 4879,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfTrig[u,x]},
          With[{d=FreeFactors[Cos[v],x]},
          -d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1,Cos[v]/d,u/Sin[v],x],x],x,Cos[v]/d]] /;
         Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Cos[v],x],u/Sin[v],x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u_, x_],
        when: {
            rubi_function_of_trig(&u_, x_).is_some_and(|v| {
                // Mathematica evaluates Sin[I*z] and Cos[I*z] to their
                // hyperbolic forms before NonfreeFactors and FunctionOfQ.
                let cos = rubi_mathematica_evaluate_active_trig_call(Symbol::COS, v.to_owned());
                let sin = rubi_mathematica_evaluate_active_trig_call(Symbol::SIN, v);
                let payload = &u_ / sin;
                rubi_function_of_q(&rubi_nonfree_factors(&cos, x_), &payload, x_)
            })
        },
        rhs: {
            let v = rubi_function_of_trig(&u_, x_).rubi_rhs();
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let cos = rubi_mathematica_evaluate_active_trig_call(Symbol::COS, v.to_owned());
            let sin = rubi_mathematica_evaluate_active_trig_call(Symbol::SIN, v);
            let ff = rubi_free_factors(&cos, x_);
            let base = &cos / &ff;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand = rubi_subst_for_factor(
                &Atom::num(1),
                &base,
                &(&u_ / sin),
                substitution_symbol,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-ff / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4880,
        source: "Int[u_.*(a_.+b_.*cos[d_.+e_.*x_]^2+c_.*sin[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
          (a+c)^p \\[Star] Int[ActivateTrig[u],x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b-c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * i_cos(d__ + e__ * x_).pow(2) + c__ * i_sin(d__ + e__ * x_).pow(2)).pow(p_),
        with: [u__, a__, b__, c__, d__, e__, p_, x_],
        optional: [u__, a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&b__ - &c__, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(&rubi_activate_trig(&u__), x_);

            rubi_star((&a__ + &c__).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_4881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4881,
        source: "Int[u_.*(a_.+b_.*tan[d_.+e_.*x_]^2+c_.*sec[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
          (a+c)^p \\[Star] Int[ActivateTrig[u],x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * i_tan(d__ + e__ * x_).pow(2) + c__ * i_sec(d__ + e__ * x_).pow(2)).pow(p_),
        with: [u__, a__, b__, c__, d__, e__, p_, x_],
        optional: [u__, a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&b__ + &c__, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(&rubi_activate_trig(&u__), x_);

            rubi_star((&a__ + &c__).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_4882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4882,
        source: "Int[u_.*(a_.+b_.*cot[d_.+e_.*x_]^2+c_.*csc[d_.+e_.*x_]^2)^p_.,x_Symbol] :=
          (a+c)^p \\[Star] Int[ActivateTrig[u],x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * i_cot(d__ + e__ * x_).pow(2) + c__ * i_csc(d__ + e__ * x_).pow(2)).pow(p_),
        with: [u__, a__, b__, c__, d__, e__, p_, x_],
        optional: [u__, a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&b__ + &c__, 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(&rubi_activate_trig(&u__), x_);

            rubi_star((&a__ + &c__).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_4883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, y__);
    rules.push(rubi_rule!(
        order: 4883,
        source: "Int[u_/y_,x_Symbol] :=
          With[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
            q*Log[RemoveContent[ActivateTrig[y],x]] /;
         Not[FalseQ[q]]] /;
        Not[InertTrigFreeQ[u]]",
        desc: "Integration by substitution and reciprocal rule for integration",
        refs: ["G&R 2.111.1.2, CRC 27, A&S 3.3.15"],
        pattern: u__ / y__,
        with: [u__, y__, x_],
        when: {
            !rubi_inert_trig_free_q(&u__)
                && {
                    let y = rubi_activate_trig(&y__);
                    let u = rubi_activate_trig(&u__);
                    rubi_derivative_divides(&y, &u, x_).is_some()
                }
        },
        rhs: {
            let y = rubi_activate_trig(&y__);
            let u = rubi_activate_trig(&u__);
            let q = rubi_derivative_divides(&y, &u, x_).rubi_rhs();

            let result = q * rubi_remove_content(&y, x_).log();
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_4884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, w__, y__);
    rules.push(rubi_rule!(
        order: 4884,
        source: "Int[u_/(y_*w_),x_Symbol] :=
          With[{q=DerivativeDivides[ActivateTrig[y*w],ActivateTrig[u],x]},
            q*Log[RemoveContent[ActivateTrig[y*w],x]] /;
         Not[FalseQ[q]]] /;
        Not[InertTrigFreeQ[u]]",
        desc: "Integration by substitution and reciprocal rule for integration",
        refs: ["G&R 2.111.1.2, CRC 27, A&S 3.3.15"],
        pattern: u__ / (y__ * w__),
        with: [u__, y__, w__, x_],
        when: {
            !rubi_inert_trig_free_q(&u__)
                && {
                    let product = rubi_activate_trig(&(&y__ * &w__));
                    let u = rubi_activate_trig(&u__);
                    rubi_derivative_divides(&product, &u, x_).is_some()
                }
        },
        rhs: {
            let product = rubi_activate_trig(&(&y__ * &w__));
            let u = rubi_activate_trig(&u__);
            let q = rubi_derivative_divides(&product, &u, x_).rubi_rhs();

            let result = q * rubi_remove_content(&product, x_).log();
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_4885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, u__, y__);
    rules.push(rubi_rule!(
        order: 4885,
        source: "Int[u_*y_^m_.,x_Symbol] :=
          With[{q=DerivativeDivides[ActivateTrig[y],ActivateTrig[u],x]},
           q*ActivateTrig[y^(m+1)]/(m+1) /;
         Not[FalseQ[q]]] /;
        FreeQ[m,x] && NeQ[m,-1] && Not[InertTrigFreeQ[u]]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.111.1.1, CRC 23, A&S 3.3.14"],
        pattern: u__ * y__.pow(m_),
        with: [u__, y__, m_, x_],
        optional: [m_],
        when: {
            freeq!(m_, x_)
                && neq!(m_, -1)
                && !rubi_inert_trig_free_q(&u__)
                && {
                    let y = rubi_activate_trig(&y__);
                    let u = rubi_activate_trig(&u__);
                    rubi_derivative_divides(&y, &u, x_).is_some()
                }
        },
        rhs: {
            let y = rubi_activate_trig(&y__);
            let u = rubi_activate_trig(&u__);
            let q = rubi_derivative_divides(&y, &u, x_).rubi_rhs();

            let result = q * rubi_activate_trig(&y__.pow(&m_ + 1)) / (&m_ + 1);
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_4886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u__, y__, z_);
    rules.push(rubi_rule!(
        order: 4886,
        source: "Int[u_*y_^m_.*z_^n_.,x_Symbol] :=
          With[{q=DerivativeDivides[ActivateTrig[y*z],ActivateTrig[u*z^(n-m)],x]},
           q*ActivateTrig[y^(m+1)*z^(m+1)]/(m+1) /;
         Not[FalseQ[q]]] /;
        FreeQ[{m,n},x] && NeQ[m,-1] && Not[InertTrigFreeQ[u]]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.111.1.1, CRC 23, A&S 3.3.14"],
        pattern: u__ * y__.pow(m_) * Atom::var(z_).pow(n_),
        with: [u__, y__, m_, z_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!([m_, n_], x_)
                && neq!(m_, -1)
                && !rubi_inert_trig_free_q(&u__)
                && {
                    let product = rubi_activate_trig(&(&y__ * &z_));
                    let payload = rubi_activate_trig(&(&u__ * z_.pow(&n_ - &m_)));
                    rubi_derivative_divides(&product, &payload, x_).is_some()
                }
        },
        rhs: {
            let product = rubi_activate_trig(&(&y__ * &z_));
            let payload = rubi_activate_trig(&(&u__ * z_.pow(&n_ - &m_)));
            let q = rubi_derivative_divides(&product, &payload, x_).rubi_rhs();

            let result = q
                * rubi_activate_trig(&(y__.pow(&m_ + 1) * z_.pow(&m_ + 1)))
                / (&m_ + 1);
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_4887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4887,
        source: "Int[u_.*(a_.*F_[c_.+d_.*x_]^p_)^n_,x_Symbol] :=
          With[{v=ActivateTrig[F[c+d*x]]},
          a^IntPart[n]*(v/NonfreeFactors[v,x])^(p*IntPart[n])*(a*v^p)^FracPart[n]/NonfreeFactors[v,x]^(p*FracPart[n]) \\[Star]
            Int[ActivateTrig[u]*NonfreeFactors[v,x]^(n*p),x]] /;
        FreeQ[{a,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && IntegerQ[p]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * capital_f_.call( c__ + d__ * x_).pow(p_)).pow(n_),
        with: [u__, a__, capital_f_, c__, d__, p_, n_, x_],
        optional: [u__, a__, c__, d__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && rubi_inert_or_builtin_trig_q(&capital_f_)
                && !integerq!(n_)
                && integerq!(p_)
        },
        rhs: {
            let v = rubi_activate_trig(&rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &c__ + &d__ * x_));
            let nonfree_factors = rubi_nonfree_factors(&v, x_);
            let int_n = rubi_int_part(&n_);
            let frac_n = rubi_frac_part(&n_);
            let recursive_integrand = rubi_activate_trig(&u__) * nonfree_factors.pow(&n_ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = a__.pow(&int_n)
                * (&v / &nonfree_factors).pow(&p_ * &int_n)
                * (&a__ * v.pow(&p_)).pow(&frac_n)
                / nonfree_factors.pow(&p_ * &frac_n);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4888,
        source: "Int[u_.*(a_.*(b_.*F_[c_.+d_.*x_])^p_)^n_.,x_Symbol] :=
          With[{v=ActivateTrig[F[c+d*x]]},
          a^IntPart[n]*(a*(b*v)^p)^FracPart[n]/(b*v)^(p*FracPart[n]) \\[Star] Int[ActivateTrig[u]*(b*v)^(n*p),x]] /;
        FreeQ[{a,b,c,d,n,p},x] && InertTrigQ[F] && Not[IntegerQ[n]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * (b__ * capital_f_.call( c__ + d__ * x_)).pow(p_)).pow(n_),
        with: [u__, a__, b__, capital_f_, c__, d__, p_, n_, x_],
        optional: [u__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_inert_or_builtin_trig_q(&capital_f_)
                && !integerq!(n_)
                && !integerq!(p_)
        },
        rhs: {
            let v = rubi_activate_trig(&rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &c__ + &d__ * x_));
            let frac_n = rubi_frac_part(&n_);
            let recursive_integrand = rubi_activate_trig(&u__) * (&b__ * &v).pow(&n_ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = a__.pow(rubi_int_part(&n_))
                * (&a__ * (&b__ * &v).pow(&p_)).pow(&frac_n)
                / (&b__ * &v).pow(&p_ * &frac_n);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 4889,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfTrig[u,x]},
          With[{d=FreeFactors[Tan[v],x]},
          d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v]/d,u,x],x],x,Tan[v]/d]] /;
         Not[FalseQ[v]] && FunctionOfQ[NonfreeFactors[Tan[v],x],u,x]] /;
        InverseFunctionFreeQ[u,x] &&
          Not[MatchQ[u,v_.*(c_.*tan[w_]^n_.*tan[z_]^n_.)^p_. /; FreeQ[{c,p},x] && IntegerQ[n] && LinearQ[w,x] && EqQ[z,2*w]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, x_],
        when: {
            rubi_inverse_function_free_q(&u__, x_)
                && !rubi_double_angle_tangent_product_match_q(&u__, x_)
                && rubi_function_of_trig(&u__, x_).is_some_and(|v| {
                    let tan = rubi_activate_trig(&v.tan());
                    rubi_function_of_q(&rubi_nonfree_factors(&tan, x_), &u__, x_)
                })
        },
        rhs: {
            let v = rubi_function_of_trig(&u__, x_).rubi_rhs();
            let tan = rubi_activate_trig(&v.tan());
            let ff = rubi_free_factors(&tan, x_);
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let base = tan / &ff;
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let substitution_factor =
                Atom::num(1) / (Atom::num(1) + ff.pow(2) * sub.pow(2));
            let transformed_integrand =
                rubi_subst_for_factor(&substitution_factor, &base, &u__, substitution_symbol);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(ff / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, u__, v__);
    rules.push(rubi_rule!(
        order: 4890,
        source: "Int[u_*(c_.*sin[v_])^m_,x_Symbol] :=
          With[{w=FunctionOfTrig[u*Sin[v/2]^(2*m)/(c*Tan[v/2])^m,x]},
          (c*Sin[v])^m*(c*Tan[v/2])^m/Sin[v/2]^(2*m) \\[Star] Int[u*Sin[v/2]^(2*m)/(c*Tan[v/2])^m,x] /;
         Not[FalseQ[w]] && FunctionOfQ[NonfreeFactors[Tan[w],x],u*Sin[v/2]^(2*m)/(c*Tan[v/2])^m,x]] /;
        FreeQ[c,x] && LinearQ[v,x] && IntegerQ[m+1/2] && Not[SumQ[u]] && InverseFunctionFreeQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_sin(Atom::var(v__))).pow(m_),
        with: [u__, c__, v__, m_, x_],
        optional: [c__],
        when: {
            freeq!(c__, x_)
                && rubi_linear_q(&v__, x_)
                && integerq!(&m_ + Atom::num(1) / Atom::num(2))
                && !rubi_sum_q(&u__)
                && rubi_inverse_function_free_q(&u__, x_)
                && {
                    let seed =
                        &u__ * (&v__ / 2).sin().pow(2 * &m_) / (&c__ * (&v__ / 2).tan()).pow(&m_);
                    rubi_function_of_trig(&seed, x_).is_some_and(|w_trig| {
                        let tan = rubi_activate_trig(&w_trig.tan());
                        rubi_function_of_q(
                            &rubi_nonfree_factors(&tan, x_),
                            &seed,
                            x_,
                        )
                    })
                }
        },
        rhs: {
            let seed = &u__ * (&v__ / 2).sin().pow(2 * &m_) / (&c__ * (&v__ / 2).tan()).pow(&m_);
            let recursive = rubi_rhs_int(&seed, x_);
            let coefficient = (&c__ * v__.sin()).pow(&m_)
                * (&c__ * (&v__ / 2).tan()).pow(&m_)
                / (&v__ / 2).sin().pow(2 * &m_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4891,
        source: "Int[u_.*(a_.*tan[c_.+d_.*x_]^n_.+b_.*sec[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
          Int[ActivateTrig[u]*Sec[c+d*x]^(n*p)*(b+a*Sin[c+d*x]^n)^p,x] /;
        FreeQ[{a,b,c,d},x] && IntegersQ[n,p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * i_tan(c__ + d__ * x_).pow(n_) + b__ * i_sec(c__ + d__ * x_).pow(n_)).pow(p_),
        with: [u__, a__, b__, c__, d__, n_, p_, x_],
        optional: [u__, a__, b__, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && integersq!([n_, p_]) },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let integrand = rubi_activate_trig(&u__)
                * angle.sec().pow(&n_ * &p_)
                * (&b__ + &a__ * angle.sin().pow(&n_)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4892,
        source: "Int[u_.*(a_.*cot[c_.+d_.*x_]^n_.+b_.*csc[c_.+d_.*x_]^n_.)^p_,x_Symbol] :=
          Int[ActivateTrig[u]*Csc[c+d*x]^(n*p)*(b+a*Cos[c+d*x]^n)^p,x] /;
        FreeQ[{a,b,c,d},x] && IntegersQ[n,p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * i_cot(c__ + d__ * x_).pow(n_) + b__ * i_csc(c__ + d__ * x_).pow(n_)).pow(p_),
        with: [u__, a__, b__, c__, d__, n_, p_, x_],
        optional: [u__, a__, b__, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && integersq!([n_, p_]) },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let integrand = rubi_activate_trig(&u__)
                * angle.csc().pow(&n_ * &p_)
                * (&b__ + &a__ * angle.cos().pow(&n_)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 4893,
        source: "Int[u_*(a_*F_[c_.+d_.*x_]^p_.+b_.*F_[c_.+d_.*x_]^q_.)^n_.,x_Symbol] :=
          Int[ActivateTrig[u*F[c+d*x]^(n*p)*(a+b*F[c+d*x]^(q-p))^n],x] /;
        FreeQ[{a,b,c,d,p,q},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * capital_f_.call( c__ + d__ * x_).pow(p_)
            + b__ * capital_f_.call( c__ + d__ * x_).pow(q_)).pow(n_),
        with: [u__, a__, b__, capital_f_, c__, d__, p_, q_, n_, x_],
        optional: [b__, c__, d__, p_, q_, n_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && rubi_inert_trig_q(&capital_f_)
                && integerq!(n_)
                && posq!(&q_ - &p_)
        },
        rhs: {
            let trig = rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &c__ + &d__ * x_);
            let integrand =
                rubi_activate_trig(&(&u__ * trig.pow(&n_ * &p_) * (&a__ + &b__ * trig.pow(&q_ - &p_)).pow(&n_)));

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, p_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 4894,
        source: "Int[u_*(a_*F_[d_.+e_.*x_]^p_.+b_.*F_[d_.+e_.*x_]^q_.+c_.*F_[d_.+e_.*x_]^r_.)^n_.,x_Symbol] :=
          Int[ActivateTrig[u*F[d+e*x]^(n*p)*(a+b*F[d+e*x]^(q-p)+c*F[d+e*x]^(r-p))^n],x] /;
        FreeQ[{a,b,c,d,e,p,q,r},x] && InertTrigQ[F] && IntegerQ[n] && PosQ[q-p] && PosQ[r-p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * capital_f_.call( d__ + e__ * x_).pow(p_)
            + b__ * capital_f_.call( d__ + e__ * x_).pow(q_)
            + c__ * capital_f_.call( d__ + e__ * x_).pow(r_)).pow(n_),
        with: [u__, a__, b__, c__, capital_f_, d__, e__, p_, q_, r_, n_, x_],
        optional: [b__, c__, d__, e__, p_, q_, r_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_, r_], x_)
                && rubi_inert_trig_q(&capital_f_)
                && integerq!(n_)
                && posq!(&q_ - &p_)
                && posq!(&r_ - &p_)
        },
        rhs: {
            let trig = rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &d__ + &e__ * x_);
            let integrand = rubi_activate_trig(
                &(&u__
                    * trig.pow(&n_ * &p_)
                    * (&a__ + &b__ * trig.pow(&q_ - &p_) + &c__ * trig.pow(&r_ - &p_)).pow(&n_)),
            );

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 4895,
        source: "Int[u_*(a_+b_.*F_[d_.+e_.*x_]^p_.+c_.*F_[d_.+e_.*x_]^q_.)^n_.,x_Symbol] :=
          Int[ActivateTrig[u*F[d+e*x]^(n*p)*(b+a*F[d+e*x]^(-p)+c*F[d+e*x]^(q-p))^n],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && InertTrigQ[F] && IntegerQ[n] && NegQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * capital_f_.call( d__ + e__ * x_).pow(p_)
            + c__ * capital_f_.call( d__ + e__ * x_).pow(q_)).pow(n_),
        with: [u__, a__, b__, c__, capital_f_, d__, e__, p_, q_, n_, x_],
        optional: [b__, c__, d__, e__, p_, q_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_inert_trig_q(&capital_f_)
                && integerq!(n_)
                && negq!(p_)
        },
        rhs: {
            let trig = rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &d__ + &e__ * x_);
            let integrand = rubi_activate_trig(
                &(&u__
                    * trig.pow(&n_ * &p_)
                    * (&b__ + &a__ * trig.pow(-&p_) + &c__ * trig.pow(&q_ - &p_)).pow(&n_)),
            );

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4896,
        source: "Int[u_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[ActivateTrig[u]*(a*E^(-a/b*(c+d*x)))^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[a^2+b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_),
        with: [u__, a__, b__, c__, d__, n_, x_],
        optional: [u__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let exponential = ((-&a__ / &b__) * (&c__ + &d__ * x_)).exp();
            let integrand = rubi_activate_trig(&u__) * (&a__ * exponential).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_4897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 4897,
        source: "Int[u_,x_Symbol] :=
          Int[TrigSimplify[u],x] /;
        TrigSimplifyQ[u]",
        desc: "Reduce the trigonometric expression and integrate the result.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, x_],
        when: { rubi_trig_simplify_q(&u__) },
        rhs: {
            let simplified = rubi_trig_simplify(&u__);
            rubi_rhs_int(&simplified, x_)
        },
    ));
}

fn push_rules_rule_4898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, p_, u__, v__);
    rules.push(rubi_rule!(
        order: 4898,
        source: "Int[u_.*(a_*v_)^p_,x_Symbol] :=
          With[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
          a^IntPart[p]*(a*vv)^FracPart[p]/(vv^FracPart[p]) \\[Star] Int[uu*vv^p,x]] /;
        FreeQ[{a,p},x] && Not[IntegerQ[p]] && Not[InertTrigFreeQ[v]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * v__).pow(p_),
        with: [u__, a__, v__, p_, x_],
        optional: [u__],
        when: { freeq!([a__, p_], x_) && !integerq!(p_) && !rubi_inert_trig_free_q(&v__) },
        rhs: {
            let uu = rubi_activate_trig(&u__);
            let vv = rubi_activate_trig(&v__);
            let frac_p = rubi_frac_part(&p_);
            let recursive = rubi_rhs_int(&(uu * vv.pow(&p_)), x_);
            let coefficient =
                a__.pow(rubi_int_part(&p_)) * (&a__ * &vv).pow(&frac_p) / vv.pow(&frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, u__, v_);
    rules.push(rubi_rule!(
        order: 4899,
        source: "Int[u_.*(v_^m_)^p_,x_Symbol] :=
          With[{uu=ActivateTrig[u],vv=ActivateTrig[v]},
          (vv^m)^FracPart[p]/(vv^(m*FracPart[p])) \\[Star] Int[uu*vv^(m*p),x]] /;
        FreeQ[{m,p},x] && Not[IntegerQ[p]] && Not[InertTrigFreeQ[v]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * Atom::var(v_).pow(m_).pow(p_),
        with: [u__, v_, m_, p_, x_],
        optional: [u__],
        when: { freeq!([m_, p_], x_) && !integerq!(p_) && !rubi_inert_trig_free_q(&v_) },
        rhs: {
            let uu = rubi_activate_trig(&u__);
            let vv = rubi_activate_trig(&v_);
            let frac_p = rubi_frac_part(&p_);
            let recursive = rubi_rhs_int(&(uu * vv.pow(&m_ * &p_)), x_);
            let coefficient = vv.pow(&m_).pow(&frac_p) / vv.pow(&m_ * &frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, p_, u__, v_, w__);
    rules.push(rubi_rule!(
        order: 4900,
        source: "Int[u_.*(v_^m_.*w_^n_.)^p_,x_Symbol] :=
          With[{uu=ActivateTrig[u],vv=ActivateTrig[v],ww=ActivateTrig[w]},
          (vv^m*ww^n)^FracPart[p]/(vv^(m*FracPart[p])*ww^(n*FracPart[p])) \\[Star] Int[uu*vv^(m*p)*ww^(n*p),x]] /;
        FreeQ[{m,n,p},x] && Not[IntegerQ[p]] && (Not[InertTrigFreeQ[v]] || Not[InertTrigFreeQ[w]])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (Atom::var(v_).pow(m_) * w__.pow(n_)).pow(p_),
        with: [u__, v_, m_, w__, n_, p_, x_],
        optional: [u__, n_, m_],
        when: {
            freeq!([m_, n_, p_], x_)
                && !integerq!(p_)
                && (!rubi_inert_trig_free_q(&v_) || !rubi_inert_trig_free_q(&w__))
        },
        rhs: {
            let uu = rubi_activate_trig(&u__);
            let vv = rubi_activate_trig(&v_);
            let ww = rubi_activate_trig(&w__);
            let frac_p = rubi_frac_part(&p_);
            let recursive = rubi_rhs_int(&(uu * vv.pow(&m_ * &p_) * ww.pow(&n_ * &p_)), x_);
            let coefficient = (vv.pow(&m_) * ww.pow(&n_)).pow(&frac_p)
                / (vv.pow(&m_ * &frac_p) * ww.pow(&n_ * &frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 4901,
        source: "Int[u_,x_Symbol] :=
          With[{v=ExpandTrig[u,x]},
          Int[v,x] /;
         SumQ[v]] /;
        Not[InertTrigFreeQ[u]]",
        desc: "Expand the trigonometric expression and integrate the result.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, x_],
        when: {
            !rubi_inert_trig_free_q(&u__) && {
                let v = rubi_expand_trig(&u__, x_);
                rubi_sum_q(&v)
            }
        },
        rhs: {
            let v = rubi_expand_trig(&u__, x_);
            rubi_rhs_int(&v, x_)
        },
    ));
}

fn push_rules_rule_4902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 4902,
        source: "Int[u_,x_Symbol] :=
          With[{w=Block[{$ShowSteps=False,$StepCounter=Null},
        \t\t\tInt[SubstFor[1/(1+FreeFactors[Tan[FunctionOfTrig[u,x]/2],x]^2*x^2),Tan[FunctionOfTrig[u,x]/2]/FreeFactors[Tan[FunctionOfTrig[u,x]/2],x],u,x],x]]},
          Module[{v=FunctionOfTrig[u,x],d},
          d=FreeFactors[Tan[v/2],x];
          2*d/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[1/(1+d^2*x^2),Tan[v/2]/d,u,x],x],x,Tan[v/2]/d]] /;
         CalculusFreeQ[w,x]] /;
        InverseFunctionFreeQ[u,x] && Not[FalseQ[FunctionOfTrig[u,x]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, x_],
        when: {
            rubi_inverse_function_free_q(&u__, x_)
                && rubi_function_of_trig(&u__, x_).is_some_and(|v| {
                    let tan = rubi_activate_trig(&((&v / 2).tan()));
                    let d = rubi_free_factors(&tan, x_);
                    let substitution_guard = fresh_substitution_symbol().unwrap();
                    let substitution_symbol = substitution_guard.symbol();
                    let sub = Atom::var(substitution_symbol);
                    let base = tan / &d;
                    let substitution_factor =
                        Atom::num(1) / (Atom::num(1) + d.pow(2) * sub.pow(2));
                    let transformed_integrand = rubi_subst_for_factor(
                        &substitution_factor,
                        &base,
                        &u__,
                        substitution_symbol,
                    );
                    let w = rubi_rhs_int(&transformed_integrand, substitution_symbol);

                    rubi_calculus_free_q(&w, substitution_symbol)
                })
        },
        rhs: {
            let v = rubi_function_of_trig(&u__, x_).rubi_rhs();
            let tan = rubi_activate_trig(&((&v / 2).tan()));
            let d = rubi_free_factors(&tan, x_);
            let coefficient = rubi_coefficient(&v, x_, 1).rubi_rhs();
            let base = tan / &d;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let substitution_factor =
                Atom::num(1) / (Atom::num(1) + d.pow(2) * sub.pow(2));
            let transformed_integrand = rubi_subst_for_factor(
                &substitution_factor,
                &base,
                &u__,
                substitution_symbol,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(Atom::num(2) * d / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 4903,
        source: "Int[u_,x_Symbol] :=
          With[{v=ActivateTrig[u]},
           CannotIntegrate[v,x]] /;
        Not[InertTrigFreeQ[u]]",
        desc: "Leave the integral unevaluated because no applicable rule is known.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, x_],
        when: { !rubi_inert_trig_free_q(&u__) },
        rhs: {
            let v = rubi_activate_trig(&u__);
            rubi_unintegrable(v, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4820_through_4842_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4820..=4842).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4820..=4842).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4843_through_4892_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4843..=4892).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4843..=4892).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4893_through_4903_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4893..=4903).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4893..=4903).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ * i_cos(m_ * (c__ + d__ * x_)) + b__ * i_cos(n_ * (c__ + d__ * x_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ * i_sin(m_ * (c__ + d__ * x_)) + b__ * i_cos(n_ * (c__ + d__ * x_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ * i_sin(m_ * (c__ + d__ * x_)) + b__ * i_sin(n_ * (c__ + d__ * x_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let u_ = symbols.u_;
    Atom::var(u_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let u__ = symbols.u__;
    Atom::var(u__)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let x_ = symbols.x_;
    u__ * (Atom::var(v_) + d__ * capital_f_.call(c__ * (a__ + b__ * x_)).pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).coth()
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).coth().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).tanh()
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ * (a__ + b__ * x_)).tanh().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * capital_f_.call(c__ * (a__ + b__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * capital_f_.call(c__ * (a__ + b__ * x_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * capital_f_.call(c__ * (a__ + b__ * x_)).pow(n_)
}
