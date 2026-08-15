use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7166(rules);
    push_rules_rule_7167(rules);
    push_rules_rule_7168(rules);
    push_rules_rule_7169(rules);
    push_rules_rule_7170(rules);
    push_rules_rule_7171(rules);
    push_rules_rule_7172(rules);
    push_rules_rule_7173(rules);
    push_rules_rule_7174(rules);
    push_rules_rule_7175(rules);
    push_rules_rule_7176(rules);
    push_rules_rule_7177(rules);
    push_rules_rule_7178(rules);
    push_rules_rule_7179(rules);
    push_rules_rule_7180(rules);
    push_rules_rule_7181(rules);
    push_rules_rule_7182(rules);
    push_rules_rule_7183(rules);
    push_rules_rule_7184(rules);
    push_rules_rule_7185(rules);
    push_rules_rule_7186(rules);
    push_rules_rule_7187(rules);
    push_rules_rule_7188(rules);
    push_rules_rule_7189(rules);
    push_rules_rule_7190(rules);
    push_rules_rule_7191(rules);
    push_rules_rule_7192(rules);
    push_rules_rule_7193(rules);
    push_rules_rule_7194(rules);
    push_rules_rule_7195(rules);
    push_rules_rule_7196(rules);
    push_rules_rule_7197(rules);
    push_rules_rule_7198(rules);
    push_rules_rule_7199(rules);
    push_rules_rule_7200(rules);
    push_rules_rule_7201(rules);
    push_rules_rule_7202(rules);
    push_rules_rule_7203(rules);
    push_rules_rule_7204(rules);
    push_rules_rule_7205(rules);
    push_rules_rule_7206(rules);
    push_rules_rule_7207(rules);
    push_rules_rule_7208(rules);
    push_rules_rule_7209(rules);
}

fn push_rules_rule_7166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 7166,
        source: "Int[(c_.*ProductLog[a_.+b_.*x_])^p_,x_Symbol] :=
          (a+b*x)*(c*ProductLog[a+b*x])^p/(b*(p+1)) +
          p/(c*(p+1)) \\[Star] Int[(c*ProductLog[a+b*x])^(p+1)/(1+ProductLog[a+b*x]),x] /;
        FreeQ[{a,b,c},x] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, a__, b__, p_, x_],
        optional: [c__, a__, b__],
        when: { freeq!([a__, b__, c__], x_) && ltq!(p_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let product_log = rubi_product_log(&argument);
            let scaled = &c__ * &product_log;
            rubi_simp(&(argument * scaled.pow(&p_) / (&b__ * (&p_ + 1))), x_)
                    + rubi_star(&p_, rubi_rhs_int(&(scaled.pow(&p_ + 1) / (Atom::num(1) + product_log)), x_) / (&c__ * (&p_ + 1)))
        },
    ));
}

fn push_rules_rule_7167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 7167,
        source: "Int[(c_.*ProductLog[a_.+b_.*x_])^p_.,x_Symbol] :=
          (a+b*x)*(c*ProductLog[a+b*x])^p/b -
          p \\[Star] Int[(c*ProductLog[a+b*x])^p/(1+ProductLog[a+b*x]),x] /;
        FreeQ[{a,b,c},x] && Not[LtQ[p,-1]]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, a__, b__, p_, x_],
        optional: [c__, a__, b__, p_],
        when: { freeq!([a__, b__, c__], x_) && !ltq!(p_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let product_log = rubi_product_log(&argument);
            let scaled = &c__ * &product_log;
            rubi_simp(&(argument * scaled.pow(&p_) / &b__), x_) - rubi_star(&p_, rubi_rhs_int(&(scaled.pow(&p_) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 7168,
        source: "Int[(e_.+f_.*x_)^m_.*(c_.*ProductLog[a_+b_.*x_])^p_.,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p,(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,e,f,p},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ * rubi_product_log(Atom::var(a_) + b__ * x_)).pow(p_),
        with: [e__, f__, m_, c__, a_, b__, p_, x_],
        optional: [e__, f__, c__, b__, p_, m_],
        when: { freeq!([a_, b__, c__, e__, f__, p_], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_expand_integrand_product(
                &(c__ * rubi_product_log(&sub_atom)).pow(&p_),
                &(&b__ * &e__ - &a_ * &f__ + &f__ * &sub_atom).pow(&m_),
                sub,
            );
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&integrated, sub, a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_7169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7169,
        source: "Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
          x*(c*ProductLog[a*x^n])^p -
          n*p \\[Star] Int[(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,n,p},x] && (EqQ[n*(p-1),-1] || IntegerQ[p-1/2] && EqQ[n*(p-1/2),-1])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, a__, n_, p_, x_],
        optional: [c__, a__, p_],
        when: {
            freeq!([a__, c__, n_, p_], x_)
                && (eqq!(&n_ * (&p_ - 1), -1)
                    || integerq!(&p_ - Atom::num(1) / Atom::num(2))
                        && eqq!(&n_ * (&p_ - Atom::num(1) / Atom::num(2)), -1))
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_ * scaled.pow(&p_)), x_) - rubi_star(&n_ * &p_, rubi_rhs_int(&(scaled.pow(&p_) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7170,
        source: "Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
          x*(c*ProductLog[a*x^n])^p/(n*p+1) +
          n*p/(c*(n*p+1)) \\[Star] Int[(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,n},x] && (IntegerQ[p] && EqQ[n*(p+1),-1] || IntegerQ[p-1/2] && EqQ[n*(p+1/2),-1])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, a__, n_, p_, x_],
        optional: [c__, a__, p_],
        when: {
            freeq!([a__, c__, n_], x_)
                && (integerq!(p_) && eqq!(&n_ * (&p_ + 1), -1)
                    || integerq!(&p_ - Atom::num(1) / Atom::num(2))
                        && eqq!(&n_ * (&p_ + Atom::num(1) / Atom::num(2)), -1))
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_ * scaled.pow(&p_) / (&n_ * &p_ + 1)), x_)
                    + rubi_star(&n_ * &p_ / (&c__ * (&n_ * &p_ + 1)), rubi_rhs_int(&(scaled.pow(&p_ + 1) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7171,
        source: "Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^2,x],x,1/x] /;
        FreeQ[{a,c,p},x] && ILtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, a__, n_, p_, x_],
        optional: [c__, a__, p_],
        when: { freeq!([a__, c__, p_], x_) && iltq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (c__ * rubi_product_log(&a__ * sub_atom.pow(-&n_))).pow(&p_) / sub_atom.pow(2);
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7172,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(c*ProductLog[a*x^n])^p/(m+1) -
          n*p/(m+1) \\[Star] Int[x^m*(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,m,n,p},x] && NeQ[m,-1] &&
        (IntegerQ[p-1/2] && IGtQ[2*Simplify[p+(m+1)/n],0] || Not[IntegerQ[p-1/2]] && IGtQ[Simplify[p+(m+1)/n]+1,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, c__, a__, n_, p_, x_],
        optional: [m_, c__, a__, n_, p_],
        when: {
            let shift = rubi_simplify(&(&p_ + (&m_ + 1) / &n_));
            freeq!([a__, c__, m_, n_, p_], x_)
                && neq!(m_, -1)
                && (integerq!(&p_ - Atom::num(1) / Atom::num(2)) && igtq!(Atom::num(2) * &shift, 0)
                    || !integerq!(&p_ - Atom::num(1) / Atom::num(2)) && igtq!(shift + 1, 0))
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_.pow(&m_ + 1) * scaled.pow(&p_) / (&m_ + 1)), x_)
                    - rubi_star(&n_ * &p_ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7173,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(c*ProductLog[a*x^n])^p/(m+n*p+1) +
          n*p/(c*(m+n*p+1)) \\[Star] Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,m,n,p},x] &&
        (EqQ[m,-1] || IntegerQ[p-1/2] && ILtQ[Simplify[p+(m+1)/n]-1/2,0] || Not[IntegerQ[p-1/2]] && ILtQ[Simplify[p+(m+1)/n],0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, c__, a__, n_, p_, x_],
        optional: [m_, c__, a__, n_, p_],
        when: {
            let shift = rubi_simplify(&(&p_ + (&m_ + 1) / &n_));
            freeq!([a__, c__, m_, n_, p_], x_)
                && (eqq!(m_, -1)
                    || integerq!(&p_ - Atom::num(1) / Atom::num(2)) && iltq!(&shift - Atom::num(1) / Atom::num(2), 0)
                    || !integerq!(&p_ - Atom::num(1) / Atom::num(2)) && iltq!(shift, 0))
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_.pow(&m_ + 1) * scaled.pow(&p_) / (&m_ + &n_ * &p_ + 1)), x_)
                    + rubi_star(&n_ * &p_ / (&c__ * (&m_ + &n_ * &p_ + 1)), rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_ + 1) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 7174,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_.,x_Symbol] :=
          Int[x^m*(c*ProductLog[a*x])^p/(1+ProductLog[a*x]),x] +
          1/c \\[Star] Int[x^m*(c*ProductLog[a*x])^(p+1)/(1+ProductLog[a*x]),x] /;
        FreeQ[{a,c,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (c__ * rubi_product_log(a__ * x_)).pow(p_),
        with: [m_, c__, a__, p_, x_],
        optional: [m_, c__, a__, p_],
        when: { freeq!([a__, c__, m_], x_) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_);
            let scaled = &c__ * &product_log;
            rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_) / (Atom::num(1) + &product_log)), x_)
                    + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_ + 1) / (Atom::num(1) + product_log)), x_))
        },
    ));
}

fn push_rules_rule_7175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7175,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,c,p},x] && ILtQ[n,0] && IntegerQ[m] && NeQ[m,-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, c__, a__, n_, p_, x_],
        optional: [m_, c__, a__, p_],
        when: {
            freeq!([a__, c__, p_], x_)
                && iltq!(n_, 0)
                && integerq!(m_)
                && neq!(m_, -1)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (c__ * rubi_product_log(&a__ * sub_atom.pow(-&n_))).pow(&p_) / sub_atom.pow(&m_ + 2);
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d_, x_);
    rules.push(rubi_rule!(
        order: 7176,
        source: "Int[1/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
          (a+b*x)/(b*d*ProductLog[a+b*x]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ + b__ * x_)),
        with: [d_, a__, b__, x_],
        optional: [a__, b__, d_],
        when: { freeq!([a__, b__, d_], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument / (&b__ * &d_ * rubi_product_log(&argument))), x_)
        },
    ));
}

fn push_rules_rule_7177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d_, x_);
    rules.push(rubi_rule!(
        order: 7177,
        source: "Int[ProductLog[a_.+b_.*x_]/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
          d*x - Int[1/(d+d*ProductLog[a+b*x]),x] /;
        FreeQ[{a,b,d},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: rubi_product_log(a__ + b__ * x_) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ + b__ * x_)),
        with: [a__, b__, d_, x_],
        optional: [a__, b__, d_],
        when: { freeq!([a__, b__, d_], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&d_ * x_), x_) - rubi_rhs_int(&(Atom::num(1) / (&d_ + &d_ * rubi_product_log(argument))), x_)
        },
    ));
}

fn push_rules_rule_7178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, p_, x_);
    rules.push(rubi_rule!(
        order: 7178,
        source: "Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
          c*(a+b*x)*(c*ProductLog[a+b*x])^(p-1)/(b*d) -
          c*p \\[Star] Int[(c*ProductLog[a+b*x])^(p-1)/(d+d*ProductLog[a+b*x]),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, a__, b__, p_, d_, x_],
        optional: [c__, a__, b__, d_],
        when: { freeq!([a__, b__, c__, d_], x_) && gtq!(p_, 0) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let product_log = rubi_product_log(&argument);
            let scaled = &c__ * &product_log;
            rubi_simp(&(&c__ * argument * scaled.pow(&p_ - 1) / (&b__ * &d_)), x_)
                    - rubi_star(&c__ * &p_, rubi_rhs_int(&(scaled.pow(&p_ - 1) / (&d_ + &d_ * product_log)), x_))
        },
    ));
}

fn push_rules_rule_7179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d_, x_);
    rules.push(rubi_rule!(
        order: 7179,
        source: "Int[1/(ProductLog[a_.+b_.*x_]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
          ExpIntegralEi[ProductLog[a+b*x]]/(b*d) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1)
            / (rubi_product_log(a__ + b__ * x_) * (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ + b__ * x_))),
        with: [a__, b__, d_, x_],
        optional: [a__, b__, d_],
        when: { freeq!([a__, b__, d_], x_) },
        rhs: {
            let argument = rubi_product_log(&a__ + &b__ * x_);
            rubi_simp(&(rubi_exp_integral_ei(argument) / (&b__ * &d_)), x_)
        },
    ));
}

fn push_rules_rule_7180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, x_);
    rules.push(rubi_rule!(
        order: 7180,
        source: "Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
          Rt[Pi*c,2]*Erfi[Sqrt[c*ProductLog[a+b*x]]/Rt[c,2]]/(b*c*d) /;
        FreeQ[{a,b,c,d},x] && PosQ[c]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, a__, b__, d_, x_],
        optional: [c__, a__, b__, d_],
        when: { freeq!([a__, b__, c__, d_], x_) && posq!(c__) },
        rhs: {
            let product_log = rubi_product_log(&a__ + &b__ * x_);
            rubi_simp(&(rubi_rt(&(Atom::var(Symbol::PI) * &c__), 2) * rubi_erfi((&c__ * product_log).sqrt() / rubi_rt(&c__, 2))
                    / (&b__ * &c__ * &d_)), x_)
        },
    ));
}

fn push_rules_rule_7181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, x_);
    rules.push(rubi_rule!(
        order: 7181,
        source: "Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
          Rt[-Pi*c,2]*Erf[Sqrt[c*ProductLog[a+b*x]]/Rt[-c,2]]/(b*c*d) /;
        FreeQ[{a,b,c,d},x] && NegQ[c]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, a__, b__, d_, x_],
        optional: [c__, a__, b__, d_],
        when: { freeq!([a__, b__, c__, d_], x_) && negq!(c__) },
        rhs: {
            let product_log = rubi_product_log(&a__ + &b__ * x_);
            rubi_simp(&(rubi_rt(&(-Atom::var(Symbol::PI) * &c__), 2) * ((&c__ * product_log).sqrt() / rubi_rt(&(-&c__), 2)).erf()
                    / (&b__ * &c__ * &d_)), x_)
        },
    ));
}

fn push_rules_rule_7182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, p_, x_);
    rules.push(rubi_rule!(
        order: 7182,
        source: "Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
          (a+b*x)*(c*ProductLog[a+b*x])^p/(b*d*(p+1)) -
          1/(c*(p+1)) \\[Star] Int[(c*ProductLog[a+b*x])^(p+1)/(d+d*ProductLog[a+b*x]),x] /;
        FreeQ[{a,b,c,d},x] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, a__, b__, p_, d_, x_],
        optional: [c__, a__, b__, d_],
        when: { freeq!([a__, b__, c__, d_], x_) && ltq!(p_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let product_log = rubi_product_log(&argument);
            let scaled = &c__ * &product_log;
            rubi_simp(&(argument * scaled.pow(&p_) / (&b__ * &d_ * (&p_ + 1))), x_)
                    - rubi_star(Atom::num(1) / (&c__ * (&p_ + 1)), rubi_rhs_int(&(scaled.pow(&p_ + 1) / (&d_ + &d_ * product_log)), x_))
        },
    ));
}

fn push_rules_rule_7183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, p_, x_);
    rules.push(rubi_rule!(
        order: 7183,
        source: "Int[(c_.*ProductLog[a_.+b_.*x_])^p_./(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
          Gamma[p+1,-ProductLog[a+b*x]]*(c*ProductLog[a+b*x])^p/(b*d*(-ProductLog[a+b*x])^p) /;
        FreeQ[{a,b,c,d,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, a__, b__, p_, d_, x_],
        optional: [c__, a__, b__, p_, d_],
        when: { freeq!([a__, b__, c__, d_, p_], x_) },
        rhs: {
            let product_log = rubi_product_log(&a__ + &b__ * x_);
            rubi_simp(&(rubi_gamma(&p_ + 1, -&product_log) * (&c__ * &product_log).pow(&p_) / (&b__ * &d_ * (-product_log).pow(&p_))), x_)
        },
    ));
}

fn push_rules_rule_7184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, d_, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7184,
        source: "Int[(e_.+f_.*x_)^m_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[1/(d+d*ProductLog[x]),(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,d,e,f},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(Atom::var(a_) + b__ * x_)),
        with: [e__, f__, m_, d_, a_, b__, x_],
        optional: [e__, f__, b__, m_, d_],
        when: { freeq!([a_, b__, d_, e__, f__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_expand_integrand_product(
                &(Atom::num(1) / (&d_ + &d_ * rubi_product_log(&sub_atom))),
                &(&b__ * &e__ - &a_ * &f__ + &f__ * &sub_atom).pow(&m_),
                sub,
            );
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&integrated, sub, a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_7185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d_, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 7185,
        source: "Int[(e_.+f_.*x_)^m_.*(c_.*ProductLog[a_+b_.*x_])^p_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p/(d+d*ProductLog[x]),(b*e-a*f+f*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ * rubi_product_log(Atom::var(a_) + b__ * x_)).pow(p_)
            / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(Atom::var(a_) + b__ * x_)),
        with: [e__, f__, m_, c__, a_, b__, p_, d_, x_],
        optional: [e__, f__, c__, b__, p_, m_, d_],
        when: { freeq!([a_, b__, c__, d_, e__, f__, p_], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let product_log = rubi_product_log(&sub_atom);
            let payload = rubi_expand_integrand_product(
                &((&c__ * &product_log).pow(&p_) / (&d_ + &d_ * product_log)),
                &(&b__ * &e__ - &a_ * &f__ + &f__ * &sub_atom).pow(&m_),
                sub,
            );
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&integrated, sub, a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_7186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, n_, x_);
    rules.push(rubi_rule!(
        order: 7186,
        source: "Int[1/(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
          -Subst[Int[1/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
        FreeQ[{a,d},x] && ILtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::num(1) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_))),
        with: [d_, a__, n_, x_],
        optional: [a__, d_],
        when: { freeq!([a__, d_], x_) && iltq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = Atom::num(1) / (sub_atom.pow(2) * (&d_ + &d_ * rubi_product_log(&a__ * sub_atom.pow(-&n_))));
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7187,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          c*x*(c*ProductLog[a*x^n])^(p-1)/d /;
        FreeQ[{a,c,d,n,p},x] && EqQ[n*(p-1),-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, p_, d_],
        when: { freeq!([a__, c__, d_, n_, p_], x_) && eqq!(&n_ * (&p_ - 1), -1) },
        rhs: {
            let scaled = &c__ * rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(&c__ * x_ * scaled.pow(&p_ - 1) / &d_), x_)
        },
    ));
}

fn push_rules_rule_7188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7188,
        source: "Int[ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
        FreeQ[{a,d},x] && IntegerQ[p] && EqQ[n*p,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_product_log(a__ * x_.pow(n_)).pow(p_)
            / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_))),
        with: [a__, n_, p_, d_, x_],
        optional: [a__, n_, p_, d_],
        when: { freeq!([a__, d_], x_) && integerq!(p_) && eqq!(&n_ * &p_, -1) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(a__.pow(&p_) * rubi_exp_integral_ei(-&p_ * product_log) / (&d_ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7189,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          Rt[Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[c*n,2]] /;
        FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p,1/2-1/n] && PosQ[c*n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, d_],
        when: {
            freeq!([a__, c__, d_], x_)
                && integerq!(Atom::num(1) / &n_)
                && eqq!(p_, Atom::num(1) / Atom::num(2) - Atom::num(1) / &n_)
                && posq!(&c__ * &n_)
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(rubi_rt(&(Atom::var(Symbol::PI) * &c__ * &n_), 2)
                    * rubi_erfi((&c__ * product_log).sqrt() / rubi_rt(&(&c__ * &n_), 2))
                    / (&d_ * &n_ * a__.pow(Atom::num(1) / &n_) * c__.pow(Atom::num(1) / &n_))), x_)
        },
    ));
}

fn push_rules_rule_7190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7190,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          Rt[-Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[-c*n,2]] /;
        FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p,1/2-1/n] && NegQ[c*n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, d_],
        when: {
            freeq!([a__, c__, d_], x_)
                && integerq!(Atom::num(1) / &n_)
                && eqq!(p_, Atom::num(1) / Atom::num(2) - Atom::num(1) / &n_)
                && negq!(&c__ * &n_)
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(rubi_rt(&(-Atom::var(Symbol::PI) * &c__ * &n_), 2)
                    * ((&c__ * product_log).sqrt() / rubi_rt(&(-&c__ * &n_), 2)).erf()
                    / (&d_ * &n_ * a__.pow(Atom::num(1) / &n_) * c__.pow(Atom::num(1) / &n_))), x_)
        },
    ));
}

fn push_rules_rule_7191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7191,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          c*x*(c*ProductLog[a*x^n])^(p-1)/d -
          c*(n*(p-1)+1) \\[Star] Int[(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,d},x] && GtQ[n,0] && GtQ[n*(p-1)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, p_, d_],
        when: { freeq!([a__, c__, d_], x_) && gtq!(n_, 0) && gtq!(&n_ * (&p_ - 1) + 1, 0) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(&c__ * x_ * scaled.pow(&p_ - 1) / &d_), x_)
                    - rubi_star(&c__ * (&n_ * (&p_ - 1) + 1), rubi_rhs_int(&(scaled.pow(&p_ - 1) / (&d_ + &d_ * product_log)), x_))
        },
    ));
}

fn push_rules_rule_7192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7192,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          x*(c*ProductLog[a*x^n])^p/(d*(n*p+1)) -
          1/(c*(n*p+1)) \\[Star] Int[(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,d},x] && GtQ[n,0] && LtQ[n*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, p_, d_],
        when: { freeq!([a__, c__, d_], x_) && gtq!(n_, 0) && ltq!(&n_ * &p_ + 1, 0) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_ * scaled.pow(&p_) / (&d_ * (&n_ * &p_ + 1))), x_)
                    - rubi_star(Atom::num(1) / (&c__ * (&n_ * &p_ + 1)), rubi_rhs_int(&(scaled.pow(&p_ + 1) / (&d_ + &d_ * product_log)), x_))
        },
    ));
}

fn push_rules_rule_7193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7193,
        source: "Int[(c_.*ProductLog[a_.*x_^n_])^p_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
          -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
        FreeQ[{a,c,d,p},x] && ILtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, p_, d_],
        when: { freeq!([a__, c__, d_, p_], x_) && iltq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let product_log = rubi_product_log(&a__ * sub_atom.pow(-&n_));
            let payload = (&c__ * &product_log).pow(&p_) / (sub_atom.pow(2) * (&d_ + &d_ * product_log));
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, d_, m_, x_);
    rules.push(rubi_rule!(
        order: 7194,
        source: "Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
          x^(m+1)/(d*(m+1)*ProductLog[a*x]) -
          m/(m+1) \\[Star] Int[x^m/(ProductLog[a*x]*(d+d*ProductLog[a*x])),x] /;
        FreeQ[{a,d},x] && GtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [m_, d_, a__, x_],
        optional: [m_, a__, d_],
        when: { freeq!([a__, d_], x_) && gtq!(m_, 0) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_);
            rubi_simp(&(x_.pow(&m_ + 1) / (&d_ * (&m_ + 1) * &product_log)), x_)
                    - rubi_star(&m_, rubi_rhs_int(&(x_.pow(&m_) / (product_log * (&d_ + &d_ * rubi_product_log(&a__ * x_)))), x_)
                        / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, x_);
    rules.push(rubi_rule!(
        order: 7195,
        source: "Int[1/(x_*(d_+d_.*ProductLog[a_.*x_])),x_Symbol] :=
          Log[ProductLog[a*x]]/d /;
        FreeQ[{a,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (x_ * (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_))),
        with: [d_, a__, x_],
        optional: [a__, d_],
        when: { freeq!([a__, d_], x_) },
        rhs: { rubi_simp(&(rubi_product_log(a__ * x_).log() / &d_), x_) },
    ));
}

fn push_rules_rule_7196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, d_, m_, x_);
    rules.push(rubi_rule!(
        order: 7196,
        source: "Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
          x^(m+1)/(d*(m+1)) -
          Int[x^m*ProductLog[a*x]/(d+d*ProductLog[a*x]),x] /;
        FreeQ[{a,d},x] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [m_, d_, a__, x_],
        optional: [m_, a__, d_],
        when: { freeq!([a__, d_], x_) && ltq!(m_, -1) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_);
            rubi_simp(&(x_.pow(&m_ + 1) / (&d_ * (&m_ + 1))), x_) - rubi_rhs_int(&(x_.pow(&m_) * &product_log / (&d_ + &d_ * product_log)), x_)
        },
    ));
}

fn push_rules_rule_7197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, d_, m_, x_);
    rules.push(rubi_rule!(
        order: 7197,
        source: "Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
          x^m*Gamma[m+1,-(m+1)*ProductLog[a*x]]/
        \t(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^m) /;
        FreeQ[{a,d,m},x] && Not[IntegerQ[m]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [m_, d_, a__, x_],
        optional: [a__, m_, d_],
        when: { freeq!([a__, d_, m_], x_) && !integerq!(m_) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_);
            let gamma_argument = -(&m_ + 1) * &product_log;
            rubi_simp(&(x_.pow(&m_) * rubi_gamma(&m_ + 1, &gamma_argument)
                    / (&a__ * &d_ * (&m_ + 1) * (&m_ * &product_log).exp() * gamma_argument.pow(&m_))), x_)
        },
    ));
}

fn push_rules_rule_7198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, n_, x_);
    rules.push(rubi_rule!(
        order: 7198,
        source: "Int[1/(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
          Log[ProductLog[a*x^n]]/(d*n) /;
        FreeQ[{a,d,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (x_ * (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_)))),
        with: [d_, a__, n_, x_],
        optional: [a__, n_, d_],
        when: { freeq!([a__, d_, n_], x_) },
        rhs: { rubi_simp(&(rubi_product_log(a__ * x_.pow(&n_)).log() / (&d_ * &n_)), x_) },
    ));
}

fn push_rules_rule_7199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7199,
        source: "Int[x_^m_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
          -Subst[Int[1/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
        FreeQ[{a,d},x] && IntegerQ[m] && ILtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_))),
        with: [m_, d_, a__, n_, x_],
        optional: [m_, a__, d_],
        when: {
            freeq!([a__, d_], x_)
                && integerq!(m_)
                && iltq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = Atom::num(1) / (sub_atom.pow(&m_ + 2) * (&d_ + &d_ * rubi_product_log(&a__ * sub_atom.pow(-&n_))));
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7200,
        source: "Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
          (c*ProductLog[a*x^n])^p/(d*n*p) /;
        FreeQ[{a,c,d,n,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ * rubi_product_log(a__ * x_.pow(n_))).pow(p_)
            / (x_ * (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_)))),
        with: [c__, a__, n_, p_, d_, x_],
        optional: [c__, a__, n_, p_, d_],
        when: { freeq!([a__, c__, d_, n_, p_], x_) },
        rhs: {
            let scaled = &c__ * rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(scaled.pow(&p_) / (&d_ * &n_ * &p_)), x_)
        },
    ));
}

fn push_rules_rule_7201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7201,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) /;
        FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && EqQ[m+n*(p-1),-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, p_, d_],
        when: {
            freeq!([a__, c__, d_, m_, n_, p_], x_)
                && neq!(m_, -1)
                && eqq!(&m_ + &n_ * (&p_ - 1), -1)
        },
        rhs: {
            let scaled = &c__ * rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(&c__ * x_.pow(&m_ + 1) * scaled.pow(&p_ - 1) / (&d_ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_7202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7202,
        source: "Int[x_^m_.*ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
        FreeQ[{a,d,m,n},x] && IntegerQ[p] && EqQ[m+n*p,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(m_) * rubi_product_log(a__ * x_.pow(n_)).pow(p_)
            / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_))),
        with: [m_, a__, n_, p_, d_, x_],
        optional: [m_, a__, n_, p_, d_],
        when: { freeq!([a__, d_, m_, n_], x_) && integerq!(p_) && eqq!(&m_ + &n_ * &p_, -1) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(a__.pow(&p_) * rubi_exp_integral_ei(-&p_ * product_log) / (&d_ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7203,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          a^(p-1/2)*c^(p-1/2)*Rt[Pi*c/(p-1/2),2]*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[c/(p-1/2),2]]/(d*n) /;
        FreeQ[{a,c,d,m,n},x] && NeQ[m,-1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2),-1] && PosQ[c/(p-1/2)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, d_],
        when: {
            let half_shift = &p_ - Atom::num(1) / Atom::num(2);
            freeq!([a__, c__, d_, m_, n_], x_)
                && neq!(m_, -1)
                && integerq!(half_shift)
                && eqq!(&m_ + &n_ * &half_shift, -1)
                && posq!(&c__ / &half_shift)
        },
        rhs: {
            let half_shift = &p_ - Atom::num(1) / Atom::num(2);
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(a__.pow(&half_shift) * c__.pow(&half_shift)
                    * rubi_rt(&(Atom::var(Symbol::PI) * &c__ / &half_shift), 2)
                    * ((&c__ * product_log).sqrt() / rubi_rt(&(&c__ / half_shift), 2)).erf()
                    / (&d_ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7204,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          a^(p-1/2)*c^(p-1/2)*Rt[-Pi*c/(p-1/2),2]*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[-c/(p-1/2),2]]/(d*n) /;
        FreeQ[{a,c,d,m,n},x] && NeQ[m,-1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2),-1] && NegQ[c/(p-1/2)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, d_],
        when: {
            let half_shift = &p_ - Atom::num(1) / Atom::num(2);
            freeq!([a__, c__, d_, m_, n_], x_)
                && neq!(m_, -1)
                && integerq!(half_shift)
                && eqq!(&m_ + &n_ * &half_shift, -1)
                && negq!(&c__ / &half_shift)
        },
        rhs: {
            let half_shift = &p_ - Atom::num(1) / Atom::num(2);
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            rubi_simp(&(a__.pow(&half_shift) * c__.pow(&half_shift)
                    * rubi_rt(&(-Atom::var(Symbol::PI) * &c__ / &half_shift), 2)
                    * rubi_erfi((&c__ * product_log).sqrt() / rubi_rt(&(-&c__ / half_shift), 2))
                    / (&d_ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7205,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) -
          c*(m+n*(p-1)+1)/(m+1) \\[Star] Int[x^m*(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && GtQ[Simplify[p+(m+1)/n],1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, p_, d_],
        when: {
            freeq!([a__, c__, d_, m_, n_, p_], x_)
                && neq!(m_, -1)
                && gtq!(rubi_simplify(&(&p_ + (&m_ + 1) / &n_)), 1)
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(&c__ * x_.pow(&m_ + 1) * scaled.pow(&p_ - 1) / (&d_ * (&m_ + 1))), x_)
                    - rubi_star(&c__ * (&m_ + &n_ * (&p_ - 1) + 1) / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_ - 1) / (&d_ + &d_ * product_log)), x_))
        },
    ));
}

fn push_rules_rule_7206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7206,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          x^(m+1)*(c*ProductLog[a*x^n])^p/(d*(m+n*p+1)) -
          (m+1)/(c*(m+n*p+1)) \\[Star] Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
        FreeQ[{a,c,d,m,n,p},x] && NeQ[m,-1] && LtQ[Simplify[p+(m+1)/n],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, p_, d_],
        when: {
            freeq!([a__, c__, d_, m_, n_, p_], x_)
                && neq!(m_, -1)
                && ltq!(rubi_simplify(&(&p_ + (&m_ + 1) / &n_)), 0)
        },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_.pow(&n_));
            let scaled = &c__ * &product_log;
            rubi_simp(&(x_.pow(&m_ + 1) * scaled.pow(&p_) / (&d_ * (&m_ + &n_ * &p_ + 1))), x_)
                    - rubi_star(&m_ + 1, rubi_rhs_int(&(x_.pow(&m_) * scaled.pow(&p_ + 1) / (&d_ + &d_ * product_log)), x_)
                        / (&c__ * (&m_ + &n_ * &p_ + 1)))
        },
    ));
}

fn push_rules_rule_7207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d_, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 7207,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
          x^m*Gamma[m+p+1,-(m+1)*ProductLog[a*x]]*(c*ProductLog[a*x])^p/
        \t(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^(m+p)) /;
        FreeQ[{a,c,d,m,p},x] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(m_) * (c__ * rubi_product_log(a__ * x_)).pow(p_)
            / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_)),
        with: [m_, c__, a__, p_, d_, x_],
        optional: [m_, c__, a__, p_, d_],
        when: { freeq!([a__, c__, d_, m_, p_], x_) && neq!(m_, -1) },
        rhs: {
            let product_log = rubi_product_log(&a__ * x_);
            let gamma_argument = -(&m_ + 1) * &product_log;
            rubi_simp(&(x_.pow(&m_) * rubi_gamma(&m_ + &p_ + 1, &gamma_argument) * (&c__ * &product_log).pow(&p_)
                    / (&a__ * &d_ * (&m_ + 1) * (&m_ * &product_log).exp() * gamma_argument.pow(&m_ + &p_))), x_)
        },
    ));
}

fn push_rules_rule_7208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7208,
        source: "Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
          -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
        FreeQ[{a,c,d,p},x] && NeQ[m,-1] && IntegerQ[m] && LtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [m_, c__, a__, n_, p_, d_, x_],
        optional: [m_, c__, a__, n_, p_, d_],
        when: {
            freeq!([a__, c__, d_, p_], x_)
                && neq!(m_, -1)
                && integerq!(m_)
                && ltq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let product_log = rubi_product_log(&a__ * sub_atom.pow(-&n_));
            let payload = (&c__ * &product_log).pow(&p_) / (sub_atom.pow(&m_ + 2) * (&d_ + &d_ * product_log));
            let integrated = rubi_rhs_int(&payload, sub);
            -rubi_subst(&integrated, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_7209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__);
    rules.push(rubi_rule!(
        order: 7209,
        source: "Int[u_,x_Symbol] :=
          Subst[Int[SimplifyIntegrand[(x+1)*E^x*SubstFor[ProductLog[x],u,x],x],x],x,ProductLog[x]] /;
        FunctionOfQ[ProductLog[x],u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::var(u__),
        with: [u__, x_],
        when: { rubi_function_of_q(&rubi_product_log(x_), &u__, x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replacement = rubi_product_log(x_);
            let subst_for = rubi_subst_expression(&u__, &replacement, &sub_atom);
            let integrand = rubi_simplify_integrand(&((&sub_atom + 1) * &sub_atom.exp() * subst_for), sub);
            let integrated = rubi_rhs_int(&integrand, sub);
            rubi_subst(&integrated, sub, replacement)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * rubi_product_log(a__ * x_.pow(n_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * rubi_product_log(a__ * x_.pow(n_))).pow(p_)
        / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_)))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * rubi_product_log(a__ + b__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * rubi_product_log(a__ + b__ * x_)).pow(p_)
        / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ + b__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((c__ * rubi_product_log(a__ + b__ * x_)).sqrt()
            * (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ + b__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ * rubi_product_log(a__ * x_.pow(n_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ * rubi_product_log(a__ * x_.pow(n_))).pow(p_)
        / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_.pow(n_)))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let d_ = symbols.d_;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / (Atom::var(d_) + Atom::var(d_) * rubi_product_log(a__ * x_))
}
