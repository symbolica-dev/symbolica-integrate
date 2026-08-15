use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2027(rules);
    push_rules_rule_7231(rules);
    push_rules_rule_7232(rules);
    push_rules_rule_7233(rules);
    push_rules_rule_7234(rules);
    push_rules_rule_7235(rules);
    push_rules_rule_7236(rules);
    push_rules_rule_7237(rules);
    push_rules_rule_7238(rules);
    push_rules_rule_7239(rules);
    push_rules_rule_7240(rules);
    push_rules_rule_7241(rules);
    push_rules_rule_7242(rules);
    push_rules_rule_7243(rules);
    push_rules_rule_7244(rules);
    push_rules_rule_7245(rules);
    push_rules_rule_7246(rules);
    push_rules_rule_7247(rules);
    push_rules_rule_7248(rules);
    push_rules_rule_7249(rules);
    push_rules_rule_7250(rules);
    push_rules_rule_7251(rules);
    push_rules_rule_7252(rules);
    push_rules_rule_7253(rules);
    push_rules_rule_7254(rules);
    push_rules_rule_7255(rules);
    push_rules_rule_7256(rules);
    push_rules_rule_7257(rules);
    push_rules_rule_7258(rules);
    push_rules_rule_7259(rules);
    push_rules_rule_7260(rules);
    push_rules_rule_7261(rules);
    push_rules_rule_7262(rules);
    // Source block 23 has a commented-out alternative row using -c*q and x^q; keep it inactive.

    push_rules_rule_7263(rules);
    push_rules_rule_7264(rules);
    push_rules_rule_7265(rules);
    push_rules_rule_7266(rules);
    push_rules_rule_7267(rules);
    push_rules_rule_7268(rules);
    push_rules_rule_7269(rules);
    push_rules_rule_7270(rules);
    push_rules_rule_7271(rules);
    push_rules_rule_7272(rules);
    push_rules_rule_7273(rules);
    push_rules_rule_7274(rules);
    push_rules_rule_7275(rules);
    push_rules_rule_7276(rules);
    push_rules_rule_7277(rules);
    push_rules_rule_7278(rules);
    push_rules_rule_7279(rules);
    push_rules_rule_7280(rules);
    push_rules_rule_7281(rules);
    push_rules_rule_7282(rules);
    push_rules_rule_7283(rules);
    push_rules_rule_7284(rules);
    push_rules_rule_7285(rules);
    push_rules_rule_7286(rules);
    push_rules_rule_7287(rules);
    // Source block 43 has a commented-out alternative split using Rt[-b/a,2]; keep it inactive.
    push_rules_rule_7288(rules);
    push_rules_rule_7289(rules);
    push_rules_rule_7290(rules);
    push_rules_rule_7291(rules);
    push_rules_rule_7292(rules);
    push_rules_rule_7293(rules);
    push_rules_rule_7294(rules);
    push_rules_rule_7295(rules);
    push_rules_rule_7296(rules);
    push_rules_rule_7299(rules);
}

fn push_rules_rule_7231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 7231,
        source: "Int[(a_.+b_.*F_[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
          2*e*g/(C*(e*f-d*g)) \\[Star] Subst[Int[(a+b*F[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, capital_c__, capital_f_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&capital_b__ * &e__ * &g__ - &capital_c__ * (&e__ * &f__ + &d__ * &g__), 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution = (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();
            rubi_star(Atom::num(2) * &e__ * &g__ / (&capital_c__ * (&e__ * &f__ - &d__ * &g__)), rubi_subst_function_power_primitive(&a__, &b__, capital_f_, &c__, &n_, substitution))
        },
    ));
}

fn push_rules_rule_7232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 7232,
        source: "Int[(a_.+b_.*F_[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+C_.*x_^2),x_Symbol] :=
          2*e*g/(C*(e*f-d*g)) \\[Star] Subst[Int[(a+b*F[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, d__, e__, f__, g__, n_, capital_a__, capital_c__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_c__, capital_f_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution = (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();
            rubi_star(Atom::num(2) * &e__ * &g__ / (&capital_c__ * (&e__ * &f__ - &d__ * &g__)), rubi_subst_function_power_primitive(&a__, &b__, capital_f_, &c__, &n_, substitution))
        },
    ));
}

fn push_rules_rule_7233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 7233,
        source: "Int[(a_.+b_.*F_[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_/(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
          Unintegrable[(a+b*F[c*Sqrt[d+e*x]/Sqrt[f+g*x]])^n/(A+B*x+C*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && Not[IGtQ[n,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, d__, e__, f__, g__, capital_a__, capital_b__, capital_c__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, capital_c__, capital_f_, n_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&capital_b__ * &e__ * &g__ - &capital_c__ * (&e__ * &f__ + &d__ * &g__), 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let payload = (a__ + b__ * capital_f_.call(c__ * (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt())).pow(&n_)
                / (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2));
            rubi_unintegrable(payload, x_)
        },
    ));
}

fn push_rules_rule_7234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 7234,
        source: "Int[(a_.+b_.*F_[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_/(A_+C_.*x_^2),x_Symbol] :=
          Unintegrable[(a+b*F[c*Sqrt[d+e*x]/Sqrt[f+g*x]])^n/(A+C*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && Not[IGtQ[n,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, d__, e__, f__, g__, capital_c__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_c__, capital_f_, n_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let payload = (a__ + b__ * capital_f_.call(c__ * (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt())).pow(&n_)
                / (capital_a__ + capital_c__ * x_.pow(2));
            rubi_unintegrable(payload, x_)
        },
    ));
}

fn push_rules_rule_7235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, y__);
    let rule = rubi_rule!(
        order: 7235,
        source: "Int[u_/y_,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
            q*Log[RemoveContent[y,x]] /;
         Not[FalseQ[q]]]",
        desc: "Integration by substitution and reciprocal rule for integration",
        refs: ["G&R 2.111.1.2, CRC 27, A&S 3.3.15"],
        pattern: u__ / y__,
        with: [u__, y__, x_],
        when: { rubi_derivative_divides(&y__, &u__, x_).is_some() },
        rhs: {
            let result = rubi_derivative_divides(&y__, &u__, x_).rubi_rhs()
                * rubi_remove_content(&y__, x_).log();
            rubi_simp(&result, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(y__));
}

fn push_rules_rule_7236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, w__, y__);
    rules.push(rubi_rule!(
        order: 7236,
        source: "Int[u_/(y_*w_),x_Symbol] :=
          With[{q=DerivativeDivides[y*w,u,x]},
            q*Log[RemoveContent[y*w,x]] /;
         Not[FalseQ[q]]]",
        desc: "Integration by substitution and reciprocal rule for integration",
        refs: ["G&R 2.111.1.2, CRC 27, A&S 3.3.15"],
        pattern: u__ / (y__ * w__),
        with: [u__, y__, w__, x_],
        when: { rubi_derivative_divides(&(&y__ * &w__), &u__, x_).is_some() },
        rhs: {
            let product = y__ * w__;
            let result = rubi_derivative_divides(&product, &u__, x_).rubi_rhs()
                * rubi_remove_content(&product, x_).log();
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_7237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, u__, y__);
    let rule = rubi_rule!(
        order: 7237,
        source: "Int[u_*y_^m_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
           q*y^(m+1)/(m+1) /;
         Not[FalseQ[q]]] /;
        FreeQ[m,x] && NeQ[m,-1]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.111.1.1, CRC 23, A&S 3.3.14"],
        pattern: u__ * y__.pow(m_),
        with: [u__, y__, m_, x_],
        optional: [m_],
        when: { freeq!(m_, x_) && neq!(m_, -1) && rubi_derivative_divides(&y__, &u__, x_).is_some() },
        rhs: {
            let result = rubi_derivative_divides(&y__, &u__, x_).rubi_rhs()
                * y__.pow(&m_ + 1)
                / (&m_ + 1);
            rubi_simp(&result, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(y__));
}

fn push_rules_rule_7238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u__, y__, z_);
    rules.push(rubi_rule!(
        order: 7238,
        source: "Int[u_*y_^m_.*z_^n_.,x_Symbol] :=
          With[{q=DerivativeDivides[y*z,u*z^(n-m),x]},
           q*y^(m+1)*z^(m+1)/(m+1) /;
         Not[FalseQ[q]]] /;
        FreeQ[{m,n},x] && NeQ[m,-1]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.111.1.1, CRC 23, A&S 3.3.14"],
        pattern: u__ * y__.pow(m_) * Atom::var(z_).pow(n_),
        with: [u__, y__, m_, z_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!([m_, n_], x_)
                && neq!(m_, -1)
                && rubi_derivative_divides(&(&y__ * &z_), &(&u__ * z_.pow(&n_ - &m_)), x_).is_some()
        },
        rhs: {
            let product = &y__ * &z_;
            let quotient = rubi_derivative_divides(&product, &(&u__ * z_.pow(&n_ - &m_)), x_).rubi_rhs();
            let result = quotient * y__.pow(&m_ + 1) * z_.pow(&m_ + 1) / (&m_ + 1);
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_7239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7239,
        source: "Int[u_,x_Symbol] :=
          With[{v=SimplifyIntegrand[u,x]},
          Int[v,x] /;
         SimplerIntegrandQ[v,u,x]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            let simplified = rubi_simplify_integrand(&u__, x_);
            simplified != u__ && rubi_simpler_integrand_q(&simplified, &u__, x_)
        },
        rhs: {
            let simplified = rubi_simplify_integrand(&u__, x_);
            rubi_rhs_int(&simplified, x_)
        },
    ));
}

fn push_rules_rule_7240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 7240,
        source: "Int[u_.*(e_.*Sqrt[a_.+b_.*x_^n_.]+f_.*Sqrt[c_.+d_.*x_^n_.])^m_,x_Symbol] :=
          (a*e^2-c*f^2)^m \\[Star] Int[ExpandIntegrand[u*(e*Sqrt[a+b*x^n]-f*Sqrt[c+d*x^n])^(-m),x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && ILtQ[m,0] && EqQ[b*e^2-d*f^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, e__, a__, b__, n_, f__, c__, d__, m_, x_],
        optional: [u__, e__, a__, b__, n_, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && iltq!(m_, 0)
                && eqq!(&b__ * e__.pow(2) - &d__ * f__.pow(2), 0)
        },
        rhs: {
            let conjugate = &e__ * (&a__ + &b__ * x_.pow(&n_)).sqrt() - &f__ * (&c__ + &d__ * x_.pow(&n_)).sqrt();
            let expanded = rubi_expand_integrand(&(u__ * conjugate.pow(-&m_)), x_);
            rubi_star((&a__ * e__.pow(2) - &c__ * f__.pow(2)).pow(&m_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_7241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 7241,
        source: "Int[u_.*(e_.*Sqrt[a_.+b_.*x_^n_.]+f_.*Sqrt[c_.+d_.*x_^n_.])^m_,x_Symbol] :=
          (b*e^2-d*f^2)^m \\[Star] Int[ExpandIntegrand[u*x^(m*n)*(e*Sqrt[a+b*x^n]-f*Sqrt[c+d*x^n])^(-m),x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && ILtQ[m,0] && EqQ[a*e^2-c*f^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, e__, a__, b__, n_, f__, c__, d__, m_, x_],
        optional: [u__, e__, a__, b__, n_, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && iltq!(m_, 0)
                && eqq!(&a__ * e__.pow(2) - &c__ * f__.pow(2), 0)
        },
        rhs: {
            let conjugate = &e__ * (&a__ + &b__ * x_.pow(&n_)).sqrt() - &f__ * (&c__ + &d__ * x_.pow(&n_)).sqrt();
            let expanded = rubi_expand_integrand(&(u__ * x_.pow(&m_ * &n_) * conjugate.pow(-&m_)), x_);
            rubi_star((&b__ * e__.pow(2) - &d__ * f__.pow(2)).pow(&m_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_7242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, p_, u_, v__, w__);
    let rule = rubi_rule!(
        order: 7242,
        source: "Int[u_^m_.*(a_.*u_^n_+v_)^p_.*w_,x_Symbol] :=
          Int[u^(m+n*p)*(a+u^(-n)*v)^p*w,x] /;
        FreeQ[{a,m,n},x] && IntegerQ[p] && Not[GtQ[n,0]] && Not[FreeQ[v,x]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * (a__ * Atom::var(u_).pow(n_) + v__).pow(p_) * w__,
        with: [u_, m_, a__, n_, v__, p_, w__, x_],
        optional: [m_, a__, p_],
        x_free: [a__],
        when: { freeq!([a__, m_, n_], x_) && integerq!(p_) && !gtq!(n_, 0) && !freeq!(v__, x_) },
        rhs: {
            rubi_rhs_int(
                &(u_.pow(&m_ + &n_ * &p_)
                    * (a__ + u_.pow(-n_) * v__).pow(p_)
                    * w__),
                x_,
            )
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_7243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, v_, y_);
    rules.push(rubi_rule!(
        order: 7243,
        source: "Int[u_*(a_.+b_.*y_)^m_.*(c_.+d_.*v_)^n_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
           q \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[v,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_)).pow(m_) * (c__ + d__ * Atom::var(v_)).pow(n_),
        with: [u__, a__, b__, y_, m_, c__, d__, v_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(v_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * &sub).pow(&m_) * (&c__ + &d__ * &sub).pow(&n_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, u__, v_, w_, y_);
    rules.push(rubi_rule!(
        order: 7244,
        source: "Int[u_*(a_.+b_.*y_)^m_.*(c_.+d_.*v_)^n_.*(e_.+f_.*w_)^p_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
           q \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[v,y] && EqQ[w,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_)).pow(m_) * (c__ + d__ * Atom::var(v_)).pow(n_) * (e__ + f__ * Atom::var(w_)).pow(p_),
        with: [u__, a__, b__, y_, m_, c__, d__, v_, n_, e__, f__, w_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(v_, y_)
                && eqq!(w_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * &sub).pow(&m_)
                * (&c__ + &d__ * &sub).pow(&n_)
                * (&e__ + &f__ * &sub).pow(&p_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, u__, v_, w_, y_, z_
    );
    rules.push(rubi_rule!(
        order: 7245,
        source: "Int[u_*(a_.+b_.*y_)^m_.*(c_.+d_.*v_)^n_.*(e_.+f_.*w_)^p_.*(g_.+h_.*z_)^q_.,x_Symbol] :=
          With[{r=DerivativeDivides[y,u,x]},
           r \\[Star] Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x,y] /;
         Not[FalseQ[r]]] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && EqQ[v,y] && EqQ[w,y] && EqQ[z,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_)).pow(m_) * (c__ + d__ * Atom::var(v_)).pow(n_) * (e__ + f__ * Atom::var(w_)).pow(p_) * (g__ + h__ * Atom::var(z_)).pow(q_),
        with: [u__, a__, b__, y_, m_, c__, d__, v_, n_, e__, f__, w_, p_, g__, h__, z_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_], x_)
                && eqq!(v_, y_)
                && eqq!(w_, y_)
                && eqq!(z_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * &sub).pow(&m_)
                * (&c__ + &d__ * &sub).pow(&n_)
                * (&e__ + &f__ * &sub).pow(&p_)
                * (&g__ + &h__ * &sub).pow(&q_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, n_, u__, y_);
    rules.push(rubi_rule!(
        order: 7246,
        source: "Int[u_.*(a_+b_.*y_^n_),x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
           a \\[Star] Int[u,x] + b*q \\[Star] Subst[Int[x^n,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (Atom::var(a_) + b__ * Atom::var(y_).pow(n_)),
        with: [u__, a_, b__, y_, n_, x_],
        optional: [u__, b__],
        when: { freeq!([a_, b__, n_], x_) && rubi_derivative_divides(&y_, &u__, x_).is_some() },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let direct = rubi_star(a_, rubi_rhs_int(&u__, x_));
            let substituted = rubi_star(
                b__ * quotient,
                rubi_subst_integral(&sub_guard, sub.pow(&n_), y_).rubi_rhs(),
            );
            direct + substituted
        },
    ));
}

fn push_rules_rule_7247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, u__, y_);
    rules.push(rubi_rule!(
        order: 7247,
        source: "Int[u_.*(a_.+b_.*y_^n_)^p_,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
           q \\[Star] Subst[Int[(a+b*x^n)^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_).pow(n_)).pow(p_),
        with: [u__, a__, b__, y_, n_, p_, x_],
        optional: [u__, a__, b__],
        when: { freeq!([a__, b__, n_, p_], x_) && rubi_derivative_divides(&y_, &u__, x_).is_some() },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            rubi_star(quotient, rubi_subst_integral(&sub_guard, (a__ + b__ * sub.pow(n_)).pow(p_), y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, u__, v_, y_);
    rules.push(rubi_rule!(
        order: 7248,
        source: "Int[u_.*v_^m_.*(a_.+b_.*y_^n_)^p_.,x_Symbol] :=
          Module[{q,r},
            q*r \\[Star] Subst[Int[x^m*(a+b*x^n)^p,x],x,y] /;
          Not[FalseQ[r=Divides[y^m,v^m,x]]] && Not[FalseQ[q=DerivativeDivides[y,u,x]]]] /;
        FreeQ[{a,b,m,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(v_).pow(m_) * (a__ + b__ * Atom::var(y_).pow(n_)).pow(p_),
        with: [u__, v_, m_, a__, b__, y_, n_, p_, x_],
        optional: [u__, a__, b__, p_, m_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && rubi_divides(&y_.pow(&m_), &v_.pow(&m_), x_).is_some()
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let ratio = rubi_divides(&y_.pow(&m_), &v_.pow(&m_), x_).rubi_rhs();
            let inner = sub.pow(&m_) * (&a__ + &b__ * sub.pow(&n_)).pow(&p_);
            rubi_star(quotient * ratio, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, p_, u__, v_, y_);
    rules.push(rubi_rule!(
        order: 7249,
        source: "Int[u_.*(a_.+b_.*y_^n_+c_.*v_^n2_.)^p_,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
          q \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[v,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_).pow(n_) + c__ * Atom::var(v_).pow(n2_)).pow(p_),
        with: [u__, a__, b__, y_, n_, c__, v_, n2_, p_, x_],
        optional: [u__, a__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(v_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * sub.pow(&n_) + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a_, capital_b_, a__, b__, c__, n_, n2_, p_, u__, v_, w_, y_
    );
    rules.push(rubi_rule!(
        order: 7250,
        source: "Int[u_.*(A_+B_.*y_^n_)(a_.+b_.*v_^n_+c_.*w_^n2_.)^p_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
          q \\[Star] Subst[Int[(A+B*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,c,A,B,n,p},x] && EqQ[n2,2*n] && EqQ[v,y] && EqQ[w,y]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__ * (Atom::var(capital_a_) + Atom::var(capital_b_) * Atom::var(y_).pow(n_)) * (a__ + b__ * Atom::var(v_).pow(n_) + c__ * Atom::var(w_).pow(n2_)).pow(p_),
        with: [u__, capital_a_, capital_b_, y_, n_, a__, b__, v_, c__, w_, n2_, p_, x_],
        optional: [u__, capital_b_, a__, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a_, capital_b_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(v_, y_)
                && eqq!(w_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&capital_a_ + &capital_b_ * sub.pow(&n_))
                * (&a__ + &b__ * sub.pow(&n_) + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a_, capital_b_, a__, c__, n_, n2_, p_, u__, w_, y_);
    rules.push(rubi_rule!(
        order: 7251,
        source: "Int[u_.*(A_+B_.*y_^n_)(a_.+c_.*w_^n2_.)^p_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
          q \\[Star] Subst[Int[(A+B*x^n)*(a+c*x^(2*n))^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,c,A,B,n,p},x] && EqQ[n2,2*n] && EqQ[w,y]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__ * (Atom::var(capital_a_) + Atom::var(capital_b_) * Atom::var(y_).pow(n_)) * (a__ + c__ * Atom::var(w_).pow(n2_)).pow(p_),
        with: [u__, capital_a_, capital_b_, y_, n_, a__, c__, w_, n2_, p_, x_],
        optional: [u__, capital_b_, a__, c__, n2_, p_],
        when: {
            freeq!([a__, c__, capital_a_, capital_b_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(w_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&capital_a_ + &capital_b_ * sub.pow(&n_))
                * (&a__ + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, n2_, p_, u__, v_, w_, y_);
    rules.push(rubi_rule!(
        order: 7252,
        source: "Int[u_.*v_^m_.*(a_.+b_.*y_^n_+c_.*w_^n2_.)^p_.,x_Symbol] :=
          Module[{q,r},
            q*r \\[Star] Subst[Int[x^m*(a+b*x^n+c*x^(2*n))^p,x],x,y] /;
          Not[FalseQ[r=Divides[y^m,v^m,x]]] && Not[FalseQ[q=DerivativeDivides[y,u,x]]]] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && EqQ[w,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(v_).pow(m_) * (a__ + b__ * Atom::var(y_).pow(n_) + c__ * Atom::var(w_).pow(n2_)).pow(p_),
        with: [u__, v_, m_, a__, b__, y_, n_, c__, w_, n2_, p_, x_],
        optional: [u__, a__, b__, c__, m_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(w_, y_)
                && rubi_divides(&y_.pow(&m_), &v_.pow(&m_), x_).is_some()
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let ratio = rubi_divides(&y_.pow(&m_), &v_.pow(&m_), x_).rubi_rhs();
            let inner = sub.pow(&m_)
                * (&a__ + &b__ * sub.pow(&n_) + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient * ratio, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a_, capital_b_, a__, b__, c__, m_, n_, n2_, p_, u__, v_, w_, y_, z_
    );
    rules.push(rubi_rule!(
        order: 7253,
        source: "Int[u_.*z_^m_.*(A_+B_.*y_^n_)*(a_.+b_.*v_^n_+c_.*w_^n2_.)^p_.,x_Symbol] :=
          Module[{q,r},
            q*r \\[Star] Subst[Int[x^m*(A+B*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x,y] /;
          Not[FalseQ[r=Divides[y^m,z^m,x]]] && Not[FalseQ[q=DerivativeDivides[y,u,x]]]] /;
        FreeQ[{a,b,c,A,B,m,n,p},x] && EqQ[n2,2*n] && EqQ[v,y] && EqQ[w,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(z_).pow(m_) * (Atom::var(capital_a_) + Atom::var(capital_b_) * Atom::var(y_).pow(n_)) * (a__ + b__ * Atom::var(v_).pow(n_) + c__ * Atom::var(w_).pow(n2_)).pow(p_),
        with: [u__, z_, m_, capital_a_, capital_b_, y_, n_, a__, b__, v_, c__, w_, n2_, p_, x_],
        optional: [u__, capital_b_, a__, b__, c__, m_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a_, capital_b_, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(v_, y_)
                && eqq!(w_, y_)
                && rubi_divides(&y_.pow(&m_), &z_.pow(&m_), x_).is_some()
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let ratio = rubi_divides(&y_.pow(&m_), &z_.pow(&m_), x_).rubi_rhs();
            let inner = sub.pow(&m_)
                * (&capital_a_ + &capital_b_ * sub.pow(&n_))
                * (&a__ + &b__ * sub.pow(&n_) + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient * ratio, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a_, capital_b_, a__, c__, m_, n_, n2_, p_, u__, w_, y_, z_
    );
    rules.push(rubi_rule!(
        order: 7254,
        source: "Int[u_.*z_^m_.*(A_+B_.*y_^n_)*(a_.+c_.*w_^n2_.)^p_.,x_Symbol] :=
          Module[{q,r},
            q*r \\[Star] Subst[Int[x^m*(A+B*x^n)*(a+c*x^(2*n))^p,x],x,y] /;
          Not[FalseQ[r=Divides[y^m,z^m,x]]] && Not[FalseQ[q=DerivativeDivides[y,u,x]]]] /;
        FreeQ[{a,c,A,B,m,n,p},x] && EqQ[n2,2*n] && EqQ[w,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(z_).pow(m_) * (Atom::var(capital_a_) + Atom::var(capital_b_) * Atom::var(y_).pow(n_)) * (a__ + c__ * Atom::var(w_).pow(n2_)).pow(p_),
        with: [u__, z_, m_, capital_a_, capital_b_, y_, n_, a__, c__, w_, n2_, p_, x_],
        optional: [u__, capital_b_, a__, c__, m_, n2_, p_],
        when: {
            freeq!([a__, c__, capital_a_, capital_b_, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(w_, y_)
                && rubi_divides(&y_.pow(&m_), &z_.pow(&m_), x_).is_some()
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let ratio = rubi_divides(&y_.pow(&m_), &z_.pow(&m_), x_).rubi_rhs();
            let inner = sub.pow(&m_)
                * (&capital_a_ + &capital_b_ * sub.pow(&n_))
                * (&a__ + &c__ * sub.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_star(quotient * ratio, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, u__, v_, y_);
    rules.push(rubi_rule!(
        order: 7255,
        source: "Int[u_.*(a_.+b_.*y_^n_)^m_.*(c_.+d_.*v_^n_)^p_.,x_Symbol] :=
          With[{q=DerivativeDivides[y,u,x]},
          q \\[Star] Subst[Int[(a+b*x^n)^m*(c+d*x^n)^p,x],x,y] /;
         Not[FalseQ[q]]] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[v,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_).pow(n_)).pow(m_) * (c__ + d__ * Atom::var(v_).pow(n_)).pow(p_),
        with: [u__, a__, b__, y_, n_, m_, c__, d__, v_, p_, x_],
        optional: [u__, a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(v_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * sub.pow(&n_)).pow(&m_) * (&c__ + &d__ * sub.pow(&n_)).pow(&p_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, u__, v_, w_, y_
    );
    rules.push(rubi_rule!(
        order: 7256,
        source: "Int[u_.*(a_.+b_.*y_^n_)^m_.*(c_.+d_.*v_^n_)^p_.*(e_.+f_.*w_^n_)^q_.,x_Symbol] :=
          With[{r=DerivativeDivides[y,u,x]},
          r \\[Star] Subst[Int[(a+b*x^n)^m*(c+d*x^n)^p*(e+f*x^n)^q,x],x,y] /;
         Not[FalseQ[r]]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[v,y] && EqQ[w,y]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(y_).pow(n_)).pow(m_) * (c__ + d__ * Atom::var(v_).pow(n_)).pow(p_) * (e__ + f__ * Atom::var(w_).pow(n_)).pow(q_),
        with: [u__, a__, b__, y_, n_, m_, c__, d__, v_, p_, e__, f__, w_, q_, x_],
        optional: [u__, a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(v_, y_)
                && eqq!(w_, y_)
                && rubi_derivative_divides(&y_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&y_, &u__, x_).rubi_rhs();
            let inner = (&a__ + &b__ * sub.pow(&n_)).pow(&m_)
                * (&c__ + &d__ * sub.pow(&n_)).pow(&p_)
                * (&e__ + &f__ * sub.pow(&n_)).pow(&q_);
            rubi_star(quotient, rubi_subst_integral(&sub_guard, inner, y_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, u__, v_);
    rules.push(rubi_rule!(
        order: 7257,
        source: "Int[u_*F_^v_,x_Symbol] :=
          With[{q=DerivativeDivides[v,u,x]},
           q*F^v/Log[F] /;
         Not[FalseQ[q]]] /;
        FreeQ[F,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(capital_f_).pow(v_),
        with: [u__, capital_f_, v_, x_],
        when: {
            freeq!(capital_f_, x_) && rubi_derivative_divides(&v_, &u__, x_).is_some()
        },
        rhs: {
            let quotient = rubi_derivative_divides(&v_, &u__, x_).rubi_rhs();
            rubi_simp(
                &(quotient * capital_f_.pow(&v_) / capital_f_.log()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_7258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7258,
        source: "Int[u_*w_^m_.*F_^v_,x_Symbol] :=
          With[{q=DerivativeDivides[v,u,x]},
           q \\[Star] Subst[Int[x^m*F^x,x],x,v] /;
         Not[FalseQ[q]]] /;
        FreeQ[{F,m},x] && EqQ[w,v]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * Atom::var(w_).pow(m_) * Atom::var(capital_f_).pow(v_),
        with: [u__, w_, m_, capital_f_, v_, x_],
        optional: [m_],
        when: {
            freeq!([capital_f_, m_], x_)
                && eqq!(w_, v_)
                && rubi_derivative_divides(&v_, &u__, x_).is_some()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let quotient = rubi_derivative_divides(&v_, &u__, x_).rubi_rhs();
            rubi_star(quotient, rubi_subst_integral(&sub_guard, sub.pow(m_) * capital_f_.pow(sub), v_).rubi_rhs())
        },
    ));
}

fn push_rules_rule_7259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, m_, p_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7259,
        source: "Int[u_*(a_+b_.*v_^p_.*w_^p_.)^m_.,x_Symbol] :=
          With[{c=Simplify[u/(w*D[v,x]+v*D[w,x])]},
          c \\[Star] Subst[Int[(a+b*x^p)^m,x],x,v*w] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p},x] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (Atom::var(a_) + b__ * Atom::var(v_).pow(p_) * Atom::var(w_).pow(p_)).pow(m_),
        with: [u__, a_, b__, v_, p_, w_, m_, x_],
        optional: [b__, m_, p_],
        when: {
            freeq!([a_, b__, m_, p_], x_)
                && integerq!(p_)
                && {
                    let denominator = &w_ * rubi_d(&v_, x_) + &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &w_ * rubi_d(&v_, x_) + &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let substituted = rubi_subst_integral(
                &sub_guard,
                (a_ + b__ * sub.pow(p_)).pow(m_),
                v_ * w_,
            ).rubi_rhs();
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_7260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, m_, p_, q_, r_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7260,
        source: "Int[u_*(a_+b_.*v_^p_.*w_^q_.)^m_.*v_^r_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]+q*v*D[w,x])]},
          c*p/(r+1) \\[Star] Subst[Int[(a+b*x^(p/(r+1)))^m,x],x,v^(r+1)*w] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q,r},x] && EqQ[p,q*(r+1)] && NeQ[r,-1] && IntegerQ[p/(r+1)]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (Atom::var(a_) + b__ * Atom::var(v_).pow(p_) * Atom::var(w_).pow(q_)).pow(m_) * Atom::var(v_).pow(r_),
        with: [u__, a_, b__, v_, p_, w_, q_, m_, r_, x_],
        optional: [b__, m_, r_, p_, q_],
        when: {
            freeq!([a_, b__, m_, p_, q_, r_], x_)
                && eqq!(p_, &q_ * (&r_ + 1))
                && neq!(r_, -1)
                && integerq!(&p_ / (&r_ + 1))
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) + &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) + &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let inner = (a_ + b__ * sub.pow(&p_ / (&r_ + 1))).pow(m_);
            let substituted = rubi_subst_integral(&sub_guard, inner, v_.pow(&r_ + 1) * w_).rubi_rhs();
            rubi_star(coefficient * p_ / (&r_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_7261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, m_, p_, q_, r_, s_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7261,
        source: "Int[u_*(a_+b_.*v_^p_.*w_^q_.)^m_.*v_^r_.*w_^s_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]+q*v*D[w,x])]},
          c*p/(r+1) \\[Star] Subst[Int[(a+b*x^(p/(r+1)))^m,x],x,v^(r+1)*w^(s+1)] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q,r,s},x] && EqQ[p*(s+1),q*(r+1)] && NeQ[r,-1] && IntegerQ[p/(r+1)]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (Atom::var(a_) + b__ * Atom::var(v_).pow(p_) * Atom::var(w_).pow(q_)).pow(m_) * Atom::var(v_).pow(r_) * Atom::var(w_).pow(s_),
        with: [u__, a_, b__, v_, p_, w_, q_, m_, r_, s_, x_],
        optional: [b__, m_, r_, s_, p_, q_],
        when: {
            freeq!([a_, b__, m_, p_, q_, r_, s_], x_)
                && eqq!(&p_ * (&s_ + 1), &q_ * (&r_ + 1))
                && neq!(r_, -1)
                && integerq!(&p_ / (&r_ + 1))
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) + &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) + &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let inner = (a_ + b__ * sub.pow(&p_ / (&r_ + 1))).pow(m_);
            let substituted = rubi_subst_integral(
                &sub_guard,
                inner,
                v_.pow(&r_ + 1) * w_.pow(&s_ + 1),
            ).rubi_rhs();
            rubi_star(coefficient * p_ / (&r_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_7262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, p_, q_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7262,
        source: "Int[u_*(a_.*v_^p_.+b_.*w_^q_.)^m_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]-q*v*D[w,x])]},
          c*p \\[Star] Subst[Int[(b+a*x^p)^m,x],x,v*w^(m*q+1)] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q},x] && EqQ[p+q*(m*p+1),0] && IntegerQ[p] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ * Atom::var(v_).pow(p_) + b__ * Atom::var(w_).pow(q_)).pow(m_),
        with: [u__, a__, v_, p_, b__, w_, q_, m_, x_],
        optional: [a__, p_, b__, q_, m_],
        when: {
            freeq!([a__, b__, m_, p_, q_], x_)
                && eqq!(&p_ + &q_ * (&m_ * &p_ + 1), 0)
                && integerq!(p_)
                && integerq!(m_)
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            if !freeq!(coefficient, x_) {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let substituted = rubi_subst_integral(&sub_guard,
                (b__ + a__ * sub.pow(&p_)).pow(&m_),
                v_ * w_.pow(&m_ * &q_ + 1),
            ).rubi_rhs();
            rubi_star(coefficient * &p_, substituted)
        },
    ));
}

fn push_rules_rule_7263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, p_, q_, r_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7263,
        source: "Int[u_*(a_.*v_^p_.+b_.*w_^q_.)^m_.*v_^r_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]-q*v*D[w,x])]},
          -c*q \\[Star] Subst[Int[(a+b*x^q)^m,x],x,v^(m*p+r+1)*w] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q,r},x] && EqQ[p+q*(m*p+r+1),0] && IntegerQ[q] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ * Atom::var(v_).pow(p_) + b__ * Atom::var(w_).pow(q_)).pow(m_) * Atom::var(v_).pow(r_),
        with: [u__, a__, v_, p_, b__, w_, q_, m_, r_, x_],
        optional: [a__, p_, b__, q_, r_, m_],
        when: {
            freeq!([a__, b__, m_, p_, q_, r_], x_)
                && eqq!(&p_ + &q_ * (&m_ * &p_ + &r_ + 1), 0)
                && integerq!(q_)
                && integerq!(m_)
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let substituted = rubi_subst_integral(
                &sub_guard,
                (a__ + b__ * sub.pow(&q_)).pow(&m_),
                v_.pow(&m_ * &p_ + &r_ + 1) * w_,
            ).rubi_rhs();
            rubi_star(-coefficient * &q_, substituted)
        },
    ));
}

fn push_rules_rule_7264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, p_, q_, s_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7264,
        source: "Int[u_*(a_.*v_^p_.+b_.*w_^q_.)^m_.*w_^s_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]-q*v*D[w,x])]},
          -c*q/(s+1) \\[Star] Subst[Int[(a+b*x^(q/(s+1)))^m,x],x,v^(m*p+1)*w^(s+1)] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q,s},x] && EqQ[p*(s+1)+q*(m*p+1),0] && NeQ[s,-1] && IntegerQ[q/(s+1)] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ * Atom::var(v_).pow(p_) + b__ * Atom::var(w_).pow(q_)).pow(m_) * Atom::var(w_).pow(s_),
        with: [u__, a__, v_, p_, b__, w_, q_, m_, s_, x_],
        optional: [a__, p_, b__, q_, s_, m_],
        when: {
            freeq!([a__, b__, m_, p_, q_, s_], x_)
                && eqq!(&p_ * (&s_ + 1) + &q_ * (&m_ * &p_ + 1), 0)
                && neq!(s_, -1)
                && integerq!(&q_ / (&s_ + 1))
                && integerq!(m_)
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let inner = (a__ + b__ * sub.pow(&q_ / (&s_ + 1))).pow(&m_);
            let substituted =
                rubi_subst_integral(&sub_guard, inner, v_.pow(&m_ * &p_ + 1) * w_.pow(&s_ + 1)).rubi_rhs();
            rubi_star(-coefficient * q_ / (&s_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_7265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, p_, q_, r_, s_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7265,
        source: "Int[u_*(a_.*v_^p_.+b_.*w_^q_.)^m_.*v_^r_.*w_^s_.,x_Symbol] :=
          With[{c=Simplify[u/(p*w*D[v,x]-q*v*D[w,x])]},
          -c*q/(s+1) \\[Star] Subst[Int[(a+b*x^(q/(s+1)))^m,x],x,v^(m*p+r+1)*w^(s+1)] /;
         FreeQ[c,x]] /;
        FreeQ[{a,b,m,p,q,r,s},x] && EqQ[p*(s+1)+q*(m*p+r+1),0] && NeQ[s,-1] && IntegerQ[q/(s+1)] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (a__ * Atom::var(v_).pow(p_) + b__ * Atom::var(w_).pow(q_)).pow(m_) * Atom::var(v_).pow(r_) * Atom::var(w_).pow(s_),
        with: [u__, a__, v_, p_, b__, w_, q_, m_, r_, s_, x_],
        optional: [a__, p_, b__, q_, r_, s_, m_],
        when: {
            freeq!([a__, b__, m_, p_, q_, r_, s_], x_)
                && eqq!(&p_ * (&s_ + 1) + &q_ * (&m_ * &p_ + &r_ + 1), 0)
                && neq!(s_, -1)
                && integerq!(&q_ / (&s_ + 1))
                && integerq!(m_)
                && {
                    let denominator =
                        &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
                    let coefficient = rubi_simplify(&(&u__ / denominator));
                    freeq!(coefficient, x_)
                }
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = Atom::var(sub_guard.symbol());
            let denominator = &p_ * &w_ * rubi_d(&v_, x_) - &q_ * &v_ * rubi_d(&w_, x_);
            let coefficient = rubi_simplify(&(&u__ / denominator));
            let inner = (a__ + b__ * sub.pow(&q_ / (&s_ + 1))).pow(&m_);
            let substituted = rubi_subst_integral(
                &sub_guard,
                inner,
                v_.pow(&m_ * &p_ + &r_ + 1) * w_.pow(&s_ + 1),
            ).rubi_rhs();
            rubi_star(-coefficient * q_ / (&s_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_7266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, u__, x_);
    rules.push(rubi_rule!(
        order: 7266,
        source: "Int[u_*x_^m_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[SubstFor[x^(m+1),u,x],x],x,x^(m+1)] /;
        FreeQ[m,x] && NeQ[m,-1] && FunctionOfQ[x^(m+1),u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, m_, x_],
        optional: [m_],
        when: {
            let base = x_.pow(&m_ + 1);
            freeq!(m_, x_) && neq!(m_, -1) && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let base = x_.pow(&m_ + 1);
            let transformed = rubi_subst_for(&u__, &base, sub);
            let primitive = rubi_rhs_int(&transformed, sub);
            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(&primitive, sub, base))
        },
    ));
}

fn push_rules_rule_7267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7267,
        source: "Int[u_,x_Symbol] :=
          With[{lst=SubstForFractionalPowerOfLinear[u,x]},
          lst[[2]]*lst[[4]] \\[Star] Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
         Not[FalseQ[lst]] && SubstForFractionalPowerQ[u,lst[[3]],x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            fresh_substitution_symbol().is_some_and(|substitution_guard| {
                rubi_subst_for_fractional_power_of_linear(
                    &u__,
                    x_,
                    substitution_guard.symbol(),
                )
                .is_some_and(|data| rubi_subst_for_fractional_power_q(&u__, &data.base, x_))
            })
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let data = rubi_subst_for_fractional_power_of_linear(&u__, x_, sub).rubi_rhs();
            let primitive = rubi_rhs_int(&data.integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                data.base
                    .pow(Atom::num(1) / Atom::num(data.denominator)),
            );
            rubi_star(Atom::num(data.denominator) * data.multiplier, substituted)
        },
    ));
}

fn push_rules_rule_7268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7268,
        source: "Int[u_,x_Symbol] :=
          With[{lst=SubstForFractionalPowerOfQuotientOfLinears[u,x]},
          lst[[2]]*lst[[4]] \\[Star] Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
         Not[FalseQ[lst]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            fresh_substitution_symbol().is_some_and(|substitution_guard| {
                rubi_subst_for_fractional_power_of_quotient_of_linears(
                    &u__,
                    x_,
                    substitution_guard.symbol(),
                )
                .is_some()
            })
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let data = rubi_subst_for_fractional_power_of_quotient_of_linears(&u__, x_, sub).rubi_rhs();
            let primitive = rubi_rhs_int(&data.integrand, sub);
            rubi_star(Atom::num(data.denominator) * data.multiplier, rubi_subst(
                        &primitive,
                        sub,
                        data.base
                            .pow(Atom::num(1) / Atom::num(data.denominator)),
                    ))
        },
    ));
}

fn push_rules_rule_7269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, p_, q_, u__, v__, w__, z__);
    let rule = rubi_rule!(
        order: 7269,
        source: "Int[u_.*(a_.*v_^m_.*w_^n_.*z_^q_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a*v^m*w^n*z^q)^FracPart[p]/(v^(m*FracPart[p])*w^(n*FracPart[p])*z^(q*FracPart[p])) \\[Star] Int[u*v^(m*p)*w^(n*p)*z^(p*q),x] /;
        FreeQ[{a,m,n,p,q},x] && Not[IntegerQ[p]] && Not[FreeQ[v,x]] && Not[FreeQ[w,x]] && Not[FreeQ[z,x]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * v__.pow(m_) * w__.pow(n_) * z__.pow(q_)).pow(p_),
        with: [u__, a__, v__, m_, w__, n_, z__, q_, p_, x_],
        optional: [u__, a__, m_, n_, q_],
        when: {
            freeq!([a__, m_, n_, p_, q_], x_)
                && !integerq!(p_)
                && !freeq!(v__, x_)
                && !freeq!(w__, x_)
                && !freeq!(z__, x_)
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * (&a__ * v__.pow(&m_) * w__.pow(&n_) * z__.pow(&q_)).pow(&frac)
                / (v__.pow(&m_ * &frac) * w__.pow(&n_ * &frac) * z__.pow(&q_ * &frac));
            let normalized = u__ * v__.pow(&m_ * &p_) * w__.pow(&n_ * &p_) * z__.pow(&p_ * &q_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    );
    rules.push(
        rule.with_early_x_dependent(v__)
            .with_early_x_dependent(w__)
            .with_early_x_dependent(z__),
    );
}

fn push_rules_rule_7270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, p_, u__, v__, w__);
    let rule = rubi_rule!(
        order: 7270,
        source: "Int[u_.*(a_.*v_^m_.*w_^n_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a*v^m*w^n)^FracPart[p]/(v^(m*FracPart[p])*w^(n*FracPart[p])) \\[Star] Int[u*v^(m*p)*w^(n*p),x] /;
        FreeQ[{a,m,n,p},x] && Not[IntegerQ[p]] && Not[FreeQ[v,x]] && Not[FreeQ[w,x]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * v__.pow(m_) * w__.pow(n_)).pow(p_),
        with: [u__, a__, v__, m_, w__, n_, p_, x_],
        optional: [u__, a__, m_, n_],
        when: {
            freeq!([a__, m_, n_, p_], x_)
                && !integerq!(p_)
                && !freeq!(v__, x_)
                && !freeq!(w__, x_)
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * (&a__ * v__.pow(&m_) * w__.pow(&n_)).pow(&frac)
                / (v__.pow(&m_ * &frac) * w__.pow(&n_ * &frac));
            let normalized = u__ * v__.pow(&m_ * &p_) * w__.pow(&n_ * &p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(v__).with_early_x_dependent(w__));
}

fn push_rules_rule_7271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, p_, u__, v__);
    let rule = rubi_rule!(
        order: 7271,
        source: "Int[u_.*(a_.*v_^m_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a*v^m)^FracPart[p]/v^(m*FracPart[p]) \\[Star] Int[u*v^(m*p),x] /;
        FreeQ[{a,m,p},x] && Not[IntegerQ[p]] && Not[FreeQ[v,x]] && Not[EqQ[a,1] && EqQ[m,1]] && Not[EqQ[v,x] && EqQ[m,1]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * v__.pow(m_)).pow(p_),
        with: [u__, a__, v__, m_, p_, x_],
        optional: [u__, a__, m_],
        when: {
            freeq!([a__, m_, p_], x_)
                && !integerq!(p_)
                && !freeq!(v__, x_)
                && !(eqq!(a__, 1) && eqq!(m_, 1))
                && !(eqq!(v__, x_) && eqq!(m_, 1))
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * (&a__ * v__.pow(&m_)).pow(&frac)
                / v__.pow(&m_ * &frac);
            let normalized = u__ * v__.pow(&m_ * &p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_7272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7272,
        source: "Int[u_.*(a_.+b_.*x_^n_)^p_,x_Symbol] :=
          b^IntPart[p]*(a+b*x^n)^FracPart[p]/(x^(n*FracPart[p])*(1+a*x^(-n)/b)^FracPart[p]) \\[Star] Int[u*x^(n*p)*(1+a*x^(-n)/b)^p,x] /;
        FreeQ[{a,b,p},x] && Not[IntegerQ[p]] && ILtQ[n,0] && Not[RationalFunctionQ[u,x]] && IntegerQ[p+1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [u__, a__, b__, n_, p_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && !integerq!(p_)
                && iltq!(n_, 0)
                && !rubi_rational_function_q(&u__, x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = b__.pow(rubi_int_part(&p_))
                * (&a__ + &b__ * x_.pow(&n_)).pow(&frac)
                / (x_.pow(&n_ * &frac) * (Atom::num(1) + &a__ * x_.pow(-&n_) / &b__).pow(&frac));
            let normalized = u__
                * x_.pow(&n_ * &p_)
                * (Atom::num(1) + a__ * x_.pow(-n_) / b__).pow(p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, u__, v_);
    rules.push(rubi_rule!(
        order: 7273,
        source: "Int[u_.*(a_.+b_.*v_^n_)^p_,x_Symbol] :=
          (a+b*v^n)^FracPart[p]/(v^(n*FracPart[p])*(b+a*v^(-n))^FracPart[p]) \\[Star] Int[u*v^(n*p)*(b+a*v^(-n))^p,x] /;
        FreeQ[{a,b,p},x] && Not[IntegerQ[p]] && ILtQ[n,0] && BinomialQ[v,x] && Not[LinearQ[v,x]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ + b__ * Atom::var(v_).pow(n_)).pow(p_),
        with: [u__, a__, b__, v_, n_, p_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && !integerq!(p_)
                && iltq!(n_, 0)
                && rubi_binomial_q(&v_, x_)
                && !rubi_linear_q(&v_, x_)
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = (&a__ + &b__ * v_.pow(&n_)).pow(&frac)
                / (v_.pow(&n_ * &frac) * (&b__ + &a__ * v_.pow(-&n_)).pow(&frac));
            let normalized =
                u__ * v_.pow(&n_ * &p_) * (b__ + a__ * v_.pow(-n_)).pow(p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, u__, v_, x_);
    rules.push(rubi_rule!(
        order: 7274,
        source: "Int[u_.*(a_.+b_.*x_^m_.*v_^n_)^p_,x_Symbol] :=
          (a+b*x^m*v^n)^FracPart[p]/(v^(n*FracPart[p])*(b*x^m+a*v^(-n))^FracPart[p]) \\[Star] Int[u*v^(n*p)*(b*x^m+a*v^(-n))^p,x] /;
        FreeQ[{a,b,m,p},x] && Not[IntegerQ[p]] && ILtQ[n,0] && BinomialQ[v,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ + b__ * x_.pow(m_) * Atom::var(v_).pow(n_)).pow(p_),
        with: [u__, a__, b__, m_, v_, n_, p_, x_],
        optional: [u__, a__, b__, m_],
        when: {
            freeq!([a__, b__, m_, p_], x_)
                && !integerq!(p_)
                && iltq!(n_, 0)
                && rubi_binomial_q(&v_, x_)
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let multiplier = (&a__ + &b__ * x_.pow(&m_) * v_.pow(&n_)).pow(&frac)
                / (v_.pow(&n_ * &frac) * (&b__ * x_.pow(&m_) + &a__ * v_.pow(-&n_)).pow(&frac));
            let normalized = u__
                * v_.pow(&n_ * &p_)
                * (b__ * x_.pow(m_) + a__ * v_.pow(-n_)).pow(p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, r_, s_, u__, x_);
    rules.push(rubi_rule!(
        order: 7275,
        source: "Int[u_.*(a_.*x_^r_.+b_.*x_^s_.)^m_,x_Symbol] :=
          With[{v=(a*x^r+b*x^s)^FracPart[m]/(x^(r*FracPart[m])*(a+b*x^(s-r))^FracPart[m])},
          v \\[Star] Int[u*x^(m*r)*(a+b*x^(s-r))^m,x] /;
         NeQ[Simplify[v],1]] /;
        FreeQ[{a,b,m,r,s},x] && Not[IntegerQ[m]] && PosQ[s-r]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * x_.pow(r_) + b__ * x_.pow(s_)).pow(m_),
        with: [u__, a__, r_, b__, s_, m_, x_],
        optional: [u__, a__, r_, b__, s_],
        when: {
            freeq!([a__, b__, m_, r_, s_], x_)
                && !integerq!(m_)
                && posq!(&s_ - &r_)
                && {
                    let frac = rubi_frac_part(&m_);
                    let multiplier = (&a__ * x_.pow(&r_) + &b__ * x_.pow(&s_)).pow(&frac)
                        / (x_.pow(&r_ * &frac)
                            * (&a__ + &b__ * x_.pow(&s_ - &r_)).pow(&frac));
                    neq!(rubi_simplify(&multiplier), 1)
                }
        },
        rhs: {
            let frac = rubi_frac_part(&m_);
            let multiplier = (&a__ * x_.pow(&r_) + &b__ * x_.pow(&s_)).pow(&frac)
                / (x_.pow(&r_ * &frac) * (&a__ + &b__ * x_.pow(&s_ - &r_)).pow(&frac));
            let normalized = u__
                * x_.pow(&m_ * &r_)
                * (a__ + b__ * x_.pow(&s_ - &r_)).pow(m_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_2027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, r_, s_, u__, x_);
    rules.push(rubi_rule!(
        order: 2027,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.)^p_.*Fx_.,x_Symbol] :=
          Int[x^(p*r)*(a+b*x^(s-r))^p*Fx,x] /;
        FreeQ[{a,b,r,s},x] && IntegerQ[p] && PosQ[s-r] && Not[EqQ[p,1] && EqQ[u,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (a__ * x_.pow(r_) + b__ * x_.pow(s_)).pow(p_),
        with: [u__, a__, r_, b__, s_, p_, x_],
        optional: [u__, a__, r_, b__, s_, p_],
        when: {
            freeq!([a__, b__, r_, s_], x_)
                && integerq!(p_)
                && posq!(&s_ - &r_)
        },
        rhs: {
            let normalized = u__
                * x_.pow(&p_ * &r_)
                * (a__ + b__ * x_.pow(&s_ - &r_)).pow(p_);
            rubi_rhs_int(&normalized, x_)
        },
    ));
}

fn push_rules_rule_7276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 7276,
        source: "Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
          With[{v=RationalFunctionExpand[u/(a+b*x^n),x]},
          Int[v,x] /;
         SumQ[v]] /;
        FreeQ[{a,b},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ / (a__ + b__ * x_.pow(n_)),
        with: [u__, a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && rubi_rational_function_expand(&(&u__ / (&a__ + &b__ * x_.pow(&n_))), x_)
                    .is_some_and(|expanded| rubi_sum_q(&expanded))
        },
        rhs: {
            let expanded = rubi_rational_function_expand(&(&u__ / (&a__ + &b__ * x_.pow(&n_))), x_).rubi_rhs();
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_7277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7277,
        source: "Int[u_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[u*(b+2*c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p] && Not[AlgebraicFunctionQ[u,x]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [a__, b__, n_, c__, p_, n2_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
                && !rubi_algebraic_function_q(&u__, x_, false)
        },
        rhs: {
            let normalized = u__
                * (b__ + Atom::num(2) * &c__ * x_.pow(n_))
                    .pow(Atom::num(2) * &p_);
            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7278,
        source: "Int[u_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^p/(b+2*c*x^n)^(2*p) \\[Star] Int[u*(b+2*c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && Not[AlgebraicFunctionQ[u,x]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [u__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [a__, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
                && !rubi_algebraic_function_q(&u__, x_, false)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let linear = &b__ + Atom::num(2) * &c__ * x_.pow(&n_);
            let normalized = u__ * linear.pow(Atom::num(2) * &p_);
            rubi_star(trinomial.pow(&p_) / linear.pow(Atom::num(2) * &p_), rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, u__, x_);
    rules.push(rubi_rule!(
        order: 7279,
        source: "Int[u_/(a_.+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
          With[{v=RationalFunctionExpand[u/(a+b*x^n+c*x^(2*n)),x]},
          Int[v,x] /;
         SumQ[v]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)),
        with: [u__, a__, b__, n_, c__, n2_, x_],
        optional: [a__, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && rubi_rational_function_expand(
                    &(&u__
                        / (&a__
                            + &b__ * x_.pow(&n_)
                            + &c__ * x_.pow(&n2_))),
                    x_,
                )
                .is_some_and(|expanded| rubi_sum_q(&expanded))
        },
        rhs: {
            let expanded = rubi_rational_function_expand(
                &(&u__ / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(&n2_))),
                x_,
            ).rubi_rhs();
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_7280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 7280,
        source: "Int[u_./(a_.*x_^m_.+b_.*Sqrt[c_.*x_^n_]),x_Symbol] :=
          Int[u*(a*x^m-b*Sqrt[c*x^n])/(a^2*x^(2*m)-b^2*c*x^n),x] /;
        FreeQ[{a,b,c,m,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ / (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).sqrt()),
        with: [u__, a__, m_, b__, c__, n_, x_],
        optional: [u__, a__, m_, b__, c__],
        when: { freeq!([a__, b__, c__, m_, n_], x_) },
        rhs: {
            let normalized = u__
                * (&a__ * x_.pow(&m_)
                    - &b__ * (&c__ * x_.pow(&n_)).sqrt())
                / (a__.pow(2) * x_.pow(Atom::num(2) * &m_)
                    - b__.pow(2) * c__ * x_.pow(n_));
            rubi_rhs_int(&normalized, x_)
        },
    ));
}

fn push_rules_rule_7281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7281,
        source: "Int[u_,x_Symbol] :=
          With[{lst=FunctionOfLinear[u,x]},
          1/lst[[3]] \\[Star] Subst[Int[lst[[1]],x],x,lst[[2]]+lst[[3]]*x] /;
         Not[FalseQ[lst]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            fresh_substitution_symbol().is_some_and(|substitution_guard| {
                rubi_function_of_linear(&u__, x_, substitution_guard.symbol()).is_some()
            })
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let data = rubi_function_of_linear(&u__, x_, sub).rubi_rhs();
            let primitive = rubi_rhs_int(&data.integrand, sub);
            let substitution = data.constant + &data.slope * x_;
            rubi_star(Atom::num(1) / data.slope, rubi_subst(&primitive, sub, substitution))
        },
    ));
}

fn push_rules_rule_7282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, x_);
    rules.push(rubi_rule!(
        order: 7282,
        source: "Int[u_/x_,x_Symbol] :=
          With[{lst=PowerVariableExpn[u,0,x]},
          1/lst[[2]] \\[Star] Subst[Int[NormalizeIntegrand[Simplify[lst[[1]]/x],x],x],x,(lst[[3]]*x)^lst[[2]]] /;
         Not[FalseQ[lst]] && NeQ[lst[[2]],0]] /;
        NonsumQ[u] && Not[RationalFunctionQ[u,x]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ / x_,
        with: [u__, x_],
        when: {
            !rubi_sum_q(&u__)
                && !rubi_rational_function_q(&u__, x_)
                && rubi_power_variable_expn(&u__, Atom::num(0), x_).is_some_and(|data| neq!(data.power, 0))
        },
        rhs: {
            let data = rubi_power_variable_expn(&u__, Atom::num(0), x_).rubi_rhs();
            let sub = data.substitution_symbol;
            let sub_atom = Atom::var(sub);
            let normalized = rubi_normalize_integrand(
                &rubi_mathematica_simplify(&(data.integrand / &sub_atom)),
                sub,
            );
            let primitive = rubi_rhs_int(&normalized, sub);
            rubi_star(Atom::num(1) / &data.power, rubi_subst(
                    &primitive,
                    sub,
                    (data.scale * x_).pow(&data.power),
                ))
        },
    ));
}

fn push_rules_rule_7283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, u__, x_);
    rules.push(rubi_rule!(
        order: 7283,
        source: "Int[u_*x_^m_.,x_Symbol] :=
          With[{lst=PowerVariableExpn[u,m+1,x]},
          1/lst[[2]] \\[Star] Subst[Int[NormalizeIntegrand[Simplify[lst[[1]]/x],x],x],x,(lst[[3]]*x)^lst[[2]]] /;
         Not[FalseQ[lst]] && NeQ[lst[[2]],m+1]] /;
        IntegerQ[m] && NeQ[m,-1] && NonsumQ[u] && (GtQ[m,0] || Not[AlgebraicFunctionQ[u,x]])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, m_, x_],
        optional: [m_],
        when: {
            integerq!(m_)
                && neq!(m_, -1)
                && !rubi_sum_q(&u__)
                && (gtq!(m_, 0) || !rubi_algebraic_function_q(&u__, x_, false))
                && rubi_power_variable_expn(&u__, &m_ + 1, x_).is_some_and(|data| neq!(data.power, &m_ + 1))
        },
        rhs: {
            let data = rubi_power_variable_expn(&u__, &m_ + 1, x_).rubi_rhs();
            let sub = data.substitution_symbol;
            let sub_atom = Atom::var(sub);
            let normalized = rubi_normalize_integrand(
                &rubi_mathematica_simplify(&(data.integrand / &sub_atom)),
                sub,
            );
            let primitive = rubi_rhs_int(&normalized, sub);
            rubi_star(Atom::num(1) / &data.power, rubi_subst(
                    &primitive,
                    sub,
                    (data.scale * x_).pow(&data.power),
                ))
        },
    ));
}

fn push_rules_rule_7284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(fx__, m_, x_);
    rules.push(rubi_rule!(
        order: 7284,
        source: "Int[x_^m_*Fx_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*SubstPower[Fx,x,k],x],x,x^(1/k)]] /;
        FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * fx__,
        with: [m_, fx__, x_],
        when: { fractionq!(m_) },
        rhs: {
            let k = rational_denominator(&m_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_power = rubi_subst_power(&fx__, x_, k);
            let payload = sub_atom.pow(Atom::num(k) * (&m_ + 1) - 1)
                * rubi_subst(&subst_power, x_, sub_atom);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(k), rubi_subst(
                        &primitive,
                        sub,
                        x_.pow(Atom::num(1) / Atom::num(k)),
                    ))
        },
    ));
}

fn push_rules_rule_7285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7285,
        source: "Int[u_,x_Symbol] :=
          With[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
          2 \\[Star] Subst[Int[lst[[1]],x],x,lst[[2]]] /;
         Not[FalseQ[lst]] && EqQ[lst[[3]],1]] /;
        EulerIntegrandQ[u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, x_],
        when: {
            rubi_euler_integrand_q(&u__, x_)
                && rubi_function_of_square_root_of_quadratic(&u__, x_)
                    .is_some_and(|data| data.case_kind == RubiSquareRootQuadraticCase::PositiveA)
        },
        rhs: {
            let data = rubi_function_of_square_root_of_quadratic(&u__, x_).rubi_rhs();
            let sub = data.substitution_symbol;
            let primitive = rubi_rhs_int(&data.integrand, sub);
            rubi_star(Atom::num(2), rubi_subst(&primitive, sub, data.substitution))
        },
    ));
}

fn push_rules_rule_7286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7286,
        source: "Int[u_,x_Symbol] :=
          With[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
          2 \\[Star] Subst[Int[lst[[1]],x],x,lst[[2]]] /;
         Not[FalseQ[lst]] && EqQ[lst[[3]],2]] /;
        EulerIntegrandQ[u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, x_],
        when: {
            rubi_euler_integrand_q(&u__, x_)
                && rubi_function_of_square_root_of_quadratic(&u__, x_)
                    .is_some_and(|data| data.case_kind == RubiSquareRootQuadraticCase::PositiveC)
        },
        rhs: {
            let data = rubi_function_of_square_root_of_quadratic(&u__, x_).rubi_rhs();
            let sub = data.substitution_symbol;
            let primitive = rubi_rhs_int(&data.integrand, sub);
            rubi_star(Atom::num(2), rubi_subst(&primitive, sub, data.substitution))
        },
    ));
}

fn push_rules_rule_7287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7287,
        source: "Int[u_,x_Symbol] :=
          With[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
          2 \\[Star] Subst[Int[lst[[1]],x],x,lst[[2]]] /;
         Not[FalseQ[lst]] && EqQ[lst[[3]],3]] /;
        EulerIntegrandQ[u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, x_],
        when: {
            rubi_euler_integrand_q(&u__, x_)
                && rubi_function_of_square_root_of_quadratic(&u__, x_).is_some_and(|data| {
                    data.case_kind == RubiSquareRootQuadraticCase::NegativeAAndC
                })
        },
        rhs: {
            let data = rubi_function_of_square_root_of_quadratic(&u__, x_).rubi_rhs();
            let sub = data.substitution_symbol;
            let primitive = rubi_rhs_int(&data.integrand, sub);
            rubi_star(Atom::num(2), rubi_subst(&primitive, sub, data.substitution))
        },
    ));
}

fn push_rules_rule_7288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, v__);
    rules.push(rubi_rule!(
        order: 7288,
        source: "Int[1/(a_+b_.*v_^2),x_Symbol] :=
          1/(2*a) \\[Star] Int[Together[1/(1-v/Rt[-a/b,2])],x] + 1/(2*a) \\[Star] Int[Together[1/(1+v/Rt[-a/b,2])],x] /;
        FreeQ[{a,b},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: Atom::num(1) / (Atom::var(a_) + b__ * v__.pow(2)),
        with: [a_, b__, v__, x_],
        optional: [b__],
        when: { freeq!([a_, b__], x_) },
        rhs: {
            let rt = rubi_rt(&(-&a_ / &b__), 2);
            let first = rubi_simp(
                &(rubi_rhs_int(
                    &(Atom::num(1) / (Atom::num(1) - &v__ / &rt)).together(),
                    x_,
                ) / (Atom::num(2) * &a_)),
                x_,
            );
            let second = rubi_simp(
                &(rubi_rhs_int(
                    &(Atom::num(1) / (Atom::num(1) + &v__ / rt)).together(),
                    x_,
                ) / (Atom::num(2) * a_)),
                x_,
            );
            rubi_simp(&(first), x_) + rubi_simp(&(second), x_)
        },
    ));
}

fn push_rules_rule_7289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, n_, v__);
    rules.push(rubi_rule!(
        order: 7289,
        source: "Int[1/(a_+b_.*v_^n_),x_Symbol] :=
          2/(a*n) \\[Star] Sum[Int[Together[1/(1-v^2/((-1)^(4*k/n)*Rt[-a/b,n/2]))],x],{k,1,n/2}] /;
        FreeQ[{a,b},x] && IGtQ[n/2,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a_, b__, v__, n_, x_],
        optional: [b__],
        when: { freeq!([a_, b__], x_) && igtq!(&n_ / 2, 1) },
        rhs: {
            let n_int = rubi_integer_atom(&n_).rubi_rhs();
            if n_int % 2 != 0 || n_int <= 2 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
                let rt = rubi_rt(&(-&a_ / &b__), n_int / 2);
                let mut sum = Atom::num(0);
                for k in 1..=(n_int / 2) {
                    let root = Atom::num(-1).pow(Atom::num(4 * k) / Atom::num(n_int)) * &rt;
                    let term = (Atom::num(1) / (Atom::num(1) - v__.pow(2) / root)).together();
                sum += rubi_rhs_int(&term, x_);
            }
            rubi_star(Atom::num(2), sum / (&a_ * Atom::num(n_int)))
        },
    ));
}

fn push_rules_rule_7290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, n_, v__);
    rules.push(rubi_rule!(
        order: 7290,
        source: "Int[1/(a_+b_.*v_^n_),x_Symbol] :=
          1/(a*n) \\[Star] Sum[Int[Together[1/(1-v/((-1)^(2*k/n)*Rt[-a/b,n]))],x],{k,1,n}] /;
        FreeQ[{a,b},x] && IGtQ[(n-1)/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a_, b__, v__, n_, x_],
        optional: [b__],
        when: { freeq!([a_, b__], x_) && igtq!((&n_ - 1) / 2, 0) },
        rhs: {
            let n_int = rubi_integer_atom(&n_).rubi_rhs();
            if n_int <= 1 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let rt = rubi_rt(&(-&a_ / &b__), n_int);
            let mut sum = Atom::num(0);
            for k in 1..=n_int {
                let root = Atom::num(-1).pow(Atom::num(2 * k) / Atom::num(n_int)) * &rt;
                let term = (Atom::num(1) / (Atom::num(1) - &v__ / root)).together();
                sum += rubi_rhs_int(&term, x_);
            }
            rubi_star(
                Atom::num(1) / (&a_ * Atom::num(n_int)),
                sum,
            )
        },
    ));
}

fn push_rules_rule_7291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 7291,
        source: "Int[v_/(a_+b_.*u_^n_.),x_Symbol] :=
          Int[ReplaceAll[ExpandIntegrand[PolynomialInSubst[v,u,x]/(a+b*x^n),x],x->u],x] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && PolynomialInQ[v,u,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: v__ / (Atom::var(a_) + b__ * u__.pow(n_)),
        with: [v__, a_, b__, u__, n_, x_],
        optional: [b__, n_],
        when: { freeq!([a_, b__], x_) && igtq!(n_, 0) && rubi_polynomial_in_q(&v__, &u__, x_) },
        rhs: {
            let transformed = rubi_polynomial_in_subst(&v__, &u__, x_).rubi_rhs();
            let expanded = rubi_expand_integrand(&(transformed / (a_ + b__ * x_.pow(n_))), x_);
            rubi_rhs_int(&rubi_subst(&expanded, x_, u__), x_)
        },
    ));
}

fn push_rules_rule_7292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7292,
        source: "Int[u_,x_Symbol] :=
          With[{v=NormalizeIntegrand[u,x]},
          Int[v,x] /;
         v=!=u]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            let normalized = rubi_normalize_integrand(&u__, x_);
            normalized != u__
        },
        rhs: {
            let normalized = rubi_normalize_integrand(&u__, x_);
            rubi_rhs_int(&normalized, x_)
        },
    ));
}

fn push_rules_rule_7293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7293,
        source: "Int[u_,x_Symbol] :=
          With[{v=ExpandIntegrand[u,x]},
          Int[v,x] /;
         SumQ[v]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: { rubi_sum_q(&rubi_expand_integrand(&u__, x_)) },
        rhs: {
            let expanded = rubi_expand_integrand(&u__, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_7294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 7294,
        source: "Int[u_.*(a_.+b_.*x_^m_.)^p_.*(c_.+d_.*x_^n_.)^q_., x_Symbol] :=
          (a+b*x^m)^p*(c+d*x^n)^q/x^(m*p) \\[Star] Int[u*x^(m*p),x] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && EqQ[a+d,0] && EqQ[b+c,0] && EqQ[m+n,0] && EqQ[p+q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ + b__ * x_.pow(m_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_),
        with: [u__, a__, b__, m_, p_, c__, d__, n_, q_, x_],
        optional: [u__, a__, b__, m_, p_, c__, d__, n_, q_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && eqq!(&a__ + &d__, 0)
                && eqq!(&b__ + &c__, 0)
                && eqq!(&m_ + &n_, 0)
                && eqq!(&p_ + &q_, 0)
        },
        rhs: {
            let multiplier = (&a__ + &b__ * x_.pow(&m_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                / x_.pow(&m_ * &p_);
            let normalized = u__ * x_.pow(&m_ * &p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7295,
        source: "Int[u_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_, x_Symbol] :=
          Sqrt[a+b*x^n+c*x^(2*n)]/((4*c)^(p-1/2)*(b+2*c*x^n)) \\[Star] Int[u*(b+2*c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (Atom::var(a_) + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [u__, a_, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__, n2_],
        when: {
            freeq!([a_, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a_ * &c__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let trinomial = &a_ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let linear = &b__ + Atom::num(2) * &c__ * x_.pow(&n_);
            let multiplier = trinomial.sqrt()
                / ((Atom::num(4) * &c__).pow(&p_ - Atom::num(1) / Atom::num(2))
                    * &linear);
            let normalized = u__ * linear.pow(Atom::num(2) * &p_);
            rubi_star(multiplier, rubi_rhs_int(&normalized, x_))
        },
    ));
}

fn push_rules_rule_7296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7296,
        source: "Int[u_,x_Symbol] :=
          With[{lst=SubstForFractionalPowerOfLinear[u,x]},
          lst[[2]]*lst[[4]] \\[Star] Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
         Not[FalseQ[lst]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: {
            fresh_substitution_symbol().is_some_and(|substitution_guard| {
                rubi_subst_for_fractional_power_of_linear(
                    &u__,
                    x_,
                    substitution_guard.symbol(),
                )
                .is_some()
            })
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let data = rubi_subst_for_fractional_power_of_linear(&u__, x_, sub).rubi_rhs();
            let primitive = rubi_rhs_int(&data.integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                data.base
                    .pow(Atom::num(1) / Atom::num(data.denominator)),
            );
            rubi_star(Atom::num(data.denominator) * data.multiplier, substituted)
        },
    ));
}

fn push_rules_rule_7299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 7299,
        source: "Int[u_,x_] := CannotIntegrate[u,x]",
        desc: "Leave the integral unevaluated because no applicable rule is known.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: { true },
        rhs: { rubi_unintegrable(u__, x_) },
    ));
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
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * capital_f_.call(c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt())).pow(n_)
        / (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * capital_f_.call(c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt())).pow(n_)
        / (capital_a__ + capital_c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a_ = symbols.a_;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let v__ = symbols.v__;
    Atom::num(1) / (Atom::var(a_) + b__ * v__.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let u__ = symbols.u__;
    Atom::var(u__)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (e__ * (a__ + b__ * x_.pow(n_)).sqrt() + f__ * (c__ + d__ * x_.pow(n_)).sqrt()).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let m_ = symbols.m_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * x_.pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let u__ = symbols.u__;
    u__.into()
}
