use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7210(rules);
    push_rules_rule_7211(rules);
    push_rules_rule_7212(rules);
    push_rules_rule_7213(rules);
    push_rules_rule_7214(rules);
    push_rules_rule_7215(rules);
    push_rules_rule_7216(rules);
    push_rules_rule_7217(rules);
    push_rules_rule_7218(rules);
    push_rules_rule_7219(rules);
    push_rules_rule_7220(rules);
    push_rules_rule_7221(rules);
    push_rules_rule_7222(rules);
    push_rules_rule_7223(rules);
    push_rules_rule_7224(rules);
    push_rules_rule_7225(rules);
    push_rules_rule_7226(rules);
    push_rules_rule_7227(rules);
    push_rules_rule_7228(rules);
    push_rules_rule_7229(rules);
    push_rules_rule_7230(rules);
}

fn push_rules_rule_7210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f_, n_, x_);
    rules.push(rubi_rule!(
        order: 7210,
        source: "Int[Derivative[n_][f_][x_],x_Symbol] :=
          Derivative[n-1][f][x] /;
        FreeQ[{f,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.02.4"],
        pattern: rubi_derivative(Atom::var(n_), Atom::var(f_), x_),
        with: [n_, f_, x_],
        when: { freeq!([f_, n_], x_) },
        rhs: { rubi_simp(&(rubi_derivative(n_ - 1, f_, x_)), x_) },
    ));
}

fn push_rules_rule_7211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, f_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7211,
        source: "Int[(c_.*F_^(a_.+b_.*x_))^p_.*Derivative[n_][f_][x_],x_Symbol] :=
          (c*F^(a+b*x))^p*Derivative[n-1][f][x] - b*p*Log[F] \\[Star] Int[(c*F^(a+b*x))^p*Derivative[n-1][f][x],x] /;
        FreeQ[{a,b,c,f,F,p},x] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, capital_f_, a__, b__, p_, n_, f_, x_],
        optional: [c__, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, capital_f_, f_, p_], x_)
                && igtq!(n_, 0)
        },
        rhs: {
            let exponential = (&c__ * capital_f_.pow(&a__ + &b__ * x_)).pow(&p_);
            let lower_derivative = rubi_derivative(n_ - 1, f_, x_);
            rubi_simp(&(&exponential * &lower_derivative), x_)
                    - rubi_star(&b__ * &p_ * capital_f_.log(), rubi_rhs_int(&(exponential * lower_derivative), x_))
        },
    ));
}

fn push_rules_rule_7212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, f_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7212,
        source: "Int[(c_.*F_^(a_.+b_.*x_))^p_.*Derivative[n_][f_][x_],x_Symbol] :=
          (c*F^(a+b*x))^p*Derivative[n][f][x]/(b*p*Log[F]) - 1/(b*p*Log[F]) \\[Star] Int[(c*F^(a+b*x))^p*Derivative[n+1][f][x],x] /;
        FreeQ[{a,b,c,f,F,p},x] && ILtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, capital_f_, a__, b__, p_, n_, f_, x_],
        optional: [c__, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, capital_f_, f_, p_], x_)
                && iltq!(n_, 0)
        },
        rhs: {
            let exponential = (&c__ * capital_f_.pow(&a__ + &b__ * x_)).pow(&p_);
            let denominator = &b__ * &p_ * capital_f_.log();
            rubi_simp(&(&exponential * rubi_derivative(&n_, &f_, x_) / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&(exponential * rubi_derivative(n_ + 1, f_, x_)), x_))
        },
    ));
}

fn push_rules_rule_7213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, f_, n_, x_);
    rules.push(rubi_rule!(
        order: 7213,
        source: "Int[Sin[a_.+b_.*x_]*Derivative[n_][f_][x_],x_Symbol] :=
          Sin[a+b*x]*Derivative[n-1][f][x] - b \\[Star] Int[Cos[a+b*x]*Derivative[n-1][f][x],x] /;
        FreeQ[{a,b,f},x] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, f_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, f_], x_) && igtq!(n_, 0) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let lower_derivative = rubi_derivative(n_ - 1, f_, x_);
            rubi_simp(&(&angle.sin() * &lower_derivative), x_) - rubi_star(b__, rubi_rhs_int(&(angle.cos() * lower_derivative), x_))
        },
    ));
}

fn push_rules_rule_7214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, f_, n_, x_);
    rules.push(rubi_rule!(
        order: 7214,
        source: "Int[Cos[a_.+b_.*x_]*Derivative[n_][f_][x_],x_Symbol] :=
          Cos[a+b*x]*Derivative[n-1][f][x] + b \\[Star] Int[Sin[a+b*x]*Derivative[n-1][f][x],x] /;
        FreeQ[{a,b,f},x] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, f_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, f_], x_) && igtq!(n_, 0) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let lower_derivative = rubi_derivative(n_ - 1, f_, x_);
            rubi_simp(&(&angle.cos() * &lower_derivative), x_) + rubi_star(b__, rubi_rhs_int(&(angle.sin() * lower_derivative), x_))
        },
    ));
}

fn push_rules_rule_7215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, f_, n_, x_);
    rules.push(rubi_rule!(
        order: 7215,
        source: "Int[Sin[a_.+b_.*x_]*Derivative[n_][f_][x_],x_Symbol] :=
          -Cos[a+b*x]*Derivative[n][f][x]/b + 1/b \\[Star] Int[Cos[a+b*x]*Derivative[n+1][f][x],x] /;
        FreeQ[{a,b,f},x] && ILtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, f_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, f_], x_) && iltq!(n_, 0) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            rubi_simp(&(-&angle.cos() * rubi_derivative(&n_, &f_, x_) / &b__), x_)
                    + rubi_star(Atom::num(1) / b__, rubi_rhs_int(&(angle.cos() * rubi_derivative(n_ + 1, f_, x_)), x_))
        },
    ));
}

fn push_rules_rule_7216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, f_, n_, x_);
    rules.push(rubi_rule!(
        order: 7216,
        source: "Int[Cos[a_.+b_.*x_]*Derivative[n_][f_][x_],x_Symbol] :=
          Sin[a+b*x]*Derivative[n][f][x]/b - 1/b \\[Star] Int[Sin[a+b*x]*Derivative[n+1][f][x],x] /;
        FreeQ[{a,b,f},x] && ILtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, f_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, f_], x_) && iltq!(n_, 0) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            rubi_simp(&(&angle.sin() * rubi_derivative(&n_, &f_, x_) / &b__), x_)
                    - rubi_star(Atom::num(1) / b__, rubi_rhs_int(&(angle.sin() * rubi_derivative(n_ + 1, f_, x_)), x_))
        },
    ));
}

fn push_rules_rule_7217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 7217,
        source: "Int[u_*Derivative[n_][f_][x_],x_Symbol] :=
          Subst[Int[SimplifyIntegrand[SubstFor[Derivative[n-1][f][x],u,x],x],x],x,Derivative[n-1][f][x]] /;
        FreeQ[{f,n},x] && FunctionOfQ[Derivative[n-1][f][x],u,x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.02.7"],
        pattern: u__ * rubi_derivative(Atom::var(n_), Atom::var(f_), x_),
        with: [u__, n_, f_, x_],
        when: {
            freeq!([f_, n_], x_)
                && rubi_function_of_q(&rubi_derivative(&n_ - 1, &f_, x_), &u__, x_)
        },
        rhs: {
            rubi_subst_for_simplify_integrand_integral(
                &rubi_derivative(n_ - 1, f_, x_),
                &u__,
            )
        },
    ));
}

fn push_rules_rule_7218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, f_, g_, u__, x_);
    rules.push(rubi_rule!(
        order: 7218,
        source: "Int[u_*(a_.*Derivative[1][f_][x_]*g_[x_]+a_.*f_[x_]*Derivative[1][g_][x_]),x_Symbol] :=
          a \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[f[x]*g[x],u,x],x],x],x,f[x]*g[x]] /;
        FreeQ[{a,f,g},x] && FunctionOfQ[f[x]*g[x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__
            * (a__ * rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
                + a__ * f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, a__, f_, g_, x_],
        optional: [a__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            freeq!([a__, f_, g_], x_)
                && rubi_function_of_q(&(f_.call(x_) * g_.call(x_)), &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            rubi_star(a__, rubi_subst_for_simplify_integrand_integral(
                &(f_.call(x_) * g_.call(x_)),
                &u__,
            ))
        },
    ));
}

fn push_rules_rule_7219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, f_, g_, m_, m1_, u__, x_);
    rules.push(rubi_rule!(
        order: 7219,
        source: "Int[u_*(a_.*Derivative[m_][f_][x_]*g_[x_]+a_.*Derivative[m1_][f_][x_]*Derivative[1][g_][x_]),x_Symbol] :=
          a \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]*g[x],u,x],x],x],x,Derivative[m-1][f][x]*g[x]] /;
        FreeQ[{a,f,g,m},x] && EqQ[m1,m-1] && FunctionOfQ[Derivative[m-1][f][x]*g[x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__
            * (a__ * rubi_derivative(Atom::var(m_), f_, x_) * g_.call(x_)
                + a__ * rubi_derivative(Atom::var(m1_), f_, x_)
                    * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, a__, m_, f_, g_, m1_, x_],
        optional: [a__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(&m_ - 1, f_, x_) * g_.call(x_);
            freeq!([a__, f_, g_, m_], x_)
                && eqq!(m1_, &m_ - 1)
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(m_ - 1, f_, x_) * g_.call(x_);
            rubi_star(a__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, f_, g_, m_, m1_, n_, n1_, u__, x_);
    rules.push(rubi_rule!(
        order: 7220,
        source: "Int[u_*(a_.*Derivative[m_][f_][x_]*Derivative[n1_][g_][x_]+a_.*Derivative[m1_][f_][x_]*Derivative[n_][g_][x_]),x_Symbol] :=
          a \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]*Derivative[n-1][g][x],u,x],x],x],x,Derivative[m-1][f][x]*Derivative[n-1][g][x]] /;
        FreeQ[{a,f,g,m,n},x] && EqQ[m1,m-1] && EqQ[n1,n-1] && FunctionOfQ[Derivative[m-1][f][x]*Derivative[n-1][g][x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__
            * (a__ * rubi_derivative(Atom::var(m_), Atom::var(f_), x_) * rubi_derivative(Atom::var(n1_), Atom::var(g_), x_)
                + a__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_)
                    * rubi_derivative(Atom::var(n_), Atom::var(g_), x_)),
        with: [u__, a__, m_, f_, n1_, g_, m1_, n_, x_],
        optional: [a__],
        when: {
            let base = rubi_derivative(&m_ - 1, &f_, x_)
                * rubi_derivative(&n_ - 1, &g_, x_);
            freeq!([a__, f_, g_, m_, n_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(n1_, &n_ - 1)
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let base = rubi_derivative(m_ - 1, f_, x_) * rubi_derivative(n_ - 1, g_, x_);
            rubi_star(a__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7221,
        source: "Int[u_*f_[x_]^p_.*(a_.*Derivative[1][f_][x_]*g_[x_]+b_.*f_[x_]*Derivative[1][g_][x_]),x_Symbol] :=
          b \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[f[x]^(p+1)*g[x],u,x],x],x],x,f[x]^(p+1)*g[x]] /;
        FreeQ[{a,b,f,g,p},x] && EqQ[a,b*(p+1)] && FunctionOfQ[f[x]^(p+1)*g[x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * f_.call(x_).pow(p_)
            * (a__ * rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
                + b__ * f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, f_, p_, a__, g_, b__, x_],
        optional: [p_, a__, b__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = f_.call(x_).pow(&p_ + 1) * g_.call(x_);
            freeq!([a__, b__, f_, g_, p_], x_)
                && eqq!(a__, &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = f_.call(x_).pow(p_ + 1) * g_.call(x_);
            rubi_star(b__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, m_, m1_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7222,
        source: "Int[u_*Derivative[m1_][f_][x_]^p_.*
            (a_.*Derivative[m_][f_][x_]*g_[x_]+b_.*Derivative[m1_][f_][x_]*Derivative[1][g_][x_]),x_Symbol] :=
          b \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]^(p+1)*g[x],u,x],x],x],x,
            Derivative[m-1][f][x]^(p+1)*g[x]] /;
        FreeQ[{a,b,f,g,m,p},x] && EqQ[m1,m-1] && EqQ[a,b*(p+1)] && FunctionOfQ[Derivative[m-1][f][x]^(p+1)*g[x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_).pow(p_)
            * (a__ * rubi_derivative(Atom::var(m_), f_, x_) * g_.call(x_)
                + b__ * rubi_derivative(Atom::var(m1_), f_, x_)
                    * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, m1_, f_, p_, a__, m_, g_, b__, x_],
        optional: [p_, a__, b__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(&m_ - 1, f_, x_).pow(&p_ + 1) * g_.call(x_);
            freeq!([a__, b__, f_, g_, m_, p_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(a__, &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(m_ - 1, f_, x_).pow(p_ + 1) * g_.call(x_);
            rubi_star(b__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, m_, m1_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 7223,
        source: "Int[u_*g_[x_]^q_.*
            (a_.*Derivative[m_][f_][x_]*g_[x_]+b_.*Derivative[m1_][f_][x_]*Derivative[1][g_][x_]),x_Symbol] :=
          a \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]*g[x]^(q+1),u,x],x],x],x,
            Derivative[m-1][f][x]*g[x]^(q+1)] /;
        FreeQ[{a,b,f,g,m,q},x] && EqQ[m1,m-1] && EqQ[a*(q+1),b] && FunctionOfQ[Derivative[m-1][f][x]*g[x]^(q+1),u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * g_.call(x_).pow(q_)
            * (a__ * rubi_derivative(Atom::var(m_), f_, x_) * g_.call(x_)
                + b__ * rubi_derivative(Atom::var(m1_), f_, x_)
                    * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, g_, q_, a__, m_, f_, b__, m1_, x_],
        optional: [q_, a__, b__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(&m_ - 1, f_, x_) * g_.call(x_).pow(&q_ + 1);
            freeq!([a__, b__, f_, g_, m_, q_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(&a__ * (&q_ + 1), b__)
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(m_ - 1, f_, x_) * g_.call(x_).pow(q_ + 1);
            rubi_star(a__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, m_, m1_, n_, n1_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 7224,
        source: "Int[u_*Derivative[m1_][f_][x_]^p_.*
            (a_.*Derivative[m_][f_][x_]*Derivative[n1_][g_][x_]+b_.*Derivative[m1_][f_][x_]*Derivative[n_][g_][x_]),x_Symbol] :=
          b \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x],u,x],x],x],x,
            Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x]] /;
        FreeQ[{a,b,f,g,m,n,p},x] && EqQ[m1,m-1] && EqQ[n1,n-1] && EqQ[a,b*(p+1)] &&
          FunctionOfQ[Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x],u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_).pow(p_)
            * (a__ * rubi_derivative(Atom::var(m_), Atom::var(f_), x_) * rubi_derivative(Atom::var(n1_), Atom::var(g_), x_)
                + b__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_)
                    * rubi_derivative(Atom::var(n_), Atom::var(g_), x_)),
        with: [u__, m1_, f_, p_, a__, m_, n1_, g_, b__, n_, x_],
        optional: [p_, a__, b__],
        when: {
            let base = rubi_derivative(&m_ - 1, &f_, x_).pow(&p_ + 1)
                * rubi_derivative(&n_ - 1, &g_, x_);
            freeq!([a__, b__, f_, g_, m_, n_, p_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(n1_, &n_ - 1)
                && eqq!(a__, &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let base = rubi_derivative(m_ - 1, f_, x_).pow(p_ + 1)
                * rubi_derivative(n_ - 1, g_, x_);
            rubi_star(b__, rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 7225,
        source: "Int[u_*f_[x_]^p_.*g_[x_]^q_.*(a_.*Derivative[1][f_][x_]*g_[x_]+b_.*f_[x_]*Derivative[1][g_][x_]),x_Symbol] :=
          a/(p+1) \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[f[x]^(p+1)*g[x]^(q+1),u,x],x],x],x,f[x]^(p+1)*g[x]^(q+1)] /;
        FreeQ[{a,b,f,g,p,q},x] && EqQ[a*(q+1),b*(p+1)] && FunctionOfQ[f[x]^(p+1)*g[x]^(q+1),u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * f_.call(x_).pow(p_) * g_.call(x_).pow(q_)
            * (a__ * rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
                + b__ * f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, f_, p_, g_, q_, a__, b__, x_],
        optional: [p_, q_, a__, b__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = f_.call(x_).pow(&p_ + 1) * g_.call(x_).pow(&q_ + 1);
            freeq!([a__, b__, f_, g_, p_, q_], x_)
                && eqq!(&a__ * (&q_ + 1), &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = f_.call(x_).pow(&p_ + 1) * g_.call(x_).pow(&q_ + 1);
            rubi_star(a__ / (&p_ + 1), rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, m_, m1_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 7226,
        source: "Int[u_*Derivative[m1_][f_][x_]^p_.*g_[x_]^q_.*
            (a_.*Derivative[m_][f_][x_]*g_[x_]+b_.*Derivative[m1_][f_][x_]*Derivative[1][g_][x_]),x_Symbol] :=
          a/(p+1) \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]^(p+1)*g[x]^(q+1),u,x],x],x],x,
            Derivative[m-1][f][x]^(p+1)*g[x]^(q+1)] /;
        FreeQ[{a,b,f,g,m,p,q},x] && EqQ[m1,m-1] && EqQ[a*(q+1),b*(p+1)] && FunctionOfQ[Derivative[m-1][f][x]^(p+1)*g[x]^(q+1),u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * rubi_derivative(Atom::var(m1_), f_, x_).pow(p_) * g_.call(x_).pow(q_)
            * (a__ * rubi_derivative(Atom::var(m_), f_, x_) * g_.call(x_)
                + b__ * rubi_derivative(Atom::var(m1_), f_, x_)
                    * rubi_derivative(Atom::num(1), g_, x_)),
        with: [u__, m1_, f_, p_, g_, q_, a__, m_, b__, x_],
        optional: [p_, q_, a__, b__],
        when: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(&m_ - 1, &f_, x_).pow(&p_ + 1)
                * g_.call(x_).pow(&q_ + 1);
            freeq!([a__, b__, f_, g_, m_, p_, q_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(&a__ * (&q_ + 1), &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            let base = rubi_derivative(m_ - 1, f_, x_).pow(&p_ + 1)
                * g_.call(x_).pow(&q_ + 1);
            rubi_star(a__ / (&p_ + 1), rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, f_, g_, m_, m1_, n_, n1_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 7227,
        source: "Int[u_*Derivative[m1_][f_][x_]^p_.*Derivative[n1_][g_][x_]^q_.*
            (a_.*Derivative[m_][f_][x_]*Derivative[n1_][g_][x_]+b_.*Derivative[m1_][f_][x_]*Derivative[n_][g_][x_]),x_Symbol] :=
          a/(p+1) \\[Star] Subst[Int[SimplifyIntegrand[SubstFor[Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x]^(q+1),u,x],x],x],x,
            Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x]^(q+1)] /;
        FreeQ[{a,b,f,g,m,n,p,q},x] && EqQ[m1,m-1] && EqQ[n1,n-1] && EqQ[a*(q+1),b*(p+1)] &&
          FunctionOfQ[Derivative[m-1][f][x]^(p+1)*Derivative[n-1][g][x]^(q+1),u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_).pow(p_)
            * rubi_derivative(Atom::var(n1_), Atom::var(g_), x_).pow(q_)
            * (a__ * rubi_derivative(Atom::var(m_), Atom::var(f_), x_) * rubi_derivative(Atom::var(n1_), Atom::var(g_), x_)
                + b__ * rubi_derivative(Atom::var(m1_), Atom::var(f_), x_)
                    * rubi_derivative(Atom::var(n_), Atom::var(g_), x_)),
        with: [u__, m1_, f_, p_, n1_, g_, q_, a__, m_, b__, n_, x_],
        optional: [p_, q_, a__, b__],
        when: {
            let base = rubi_derivative(&m_ - 1, &f_, x_).pow(&p_ + 1)
                * rubi_derivative(&n_ - 1, &g_, x_).pow(&q_ + 1);
            freeq!([a__, b__, f_, g_, m_, n_, p_, q_], x_)
                && eqq!(m1_, &m_ - 1)
                && eqq!(n1_, &n_ - 1)
                && eqq!(&a__ * (&q_ + 1), &b__ * (&p_ + 1))
                && rubi_function_of_q(&base, &u__, x_)
        },
        rhs: {
            let base = rubi_derivative(m_ - 1, f_, x_).pow(&p_ + 1)
                * rubi_derivative(n_ - 1, g_, x_).pow(&q_ + 1);
            rubi_star(a__ / (&p_ + 1), rubi_subst_for_simplify_integrand_integral(&base, &u__))
        },
    ));
}

fn push_rules_rule_7228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f_, g_, x_);
    rules.push(rubi_rule!(
        order: 7228,
        source: "Int[f_'[x_]*g_[x_] + f_[x_]*g_'[x_],x_Symbol] :=
          f[x]*g[x] /;
        FreeQ[{f,g},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
            + f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_),
        with: [f_, g_, x_],
        when: { freeq!([f_, g_], x_) },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            rubi_simp(&(f_.call(x_) * g_.call(x_)), x_)
        },
    ));
}

fn push_rules_rule_7229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f_, g_, x_);
    rules.push(rubi_rule!(
        order: 7229,
        source: "Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/g_[x_]^2,x_Symbol] :=
          f[x]/g[x] /;
        FreeQ[{f,g},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
            - f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_))
            / g_.call(x_).pow(2),
        with: [f_, g_, x_],
        when: { freeq!([f_, g_], x_) },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            rubi_simp(&(f_.call(x_) / g_.call(x_)), x_)
        },
    ));
}

fn push_rules_rule_7230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f_, g_, x_);
    rules.push(rubi_rule!(
        order: 7230,
        source: "Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/(f_[x_]*g_[x_]),x_Symbol] :=
          Log[f[x]/g[x]] /;
        FreeQ[{f,g},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (rubi_derivative(Atom::num(1), f_, x_) * g_.call(x_)
            - f_.call(x_) * rubi_derivative(Atom::num(1), g_, x_))
            / (f_.call(x_) * g_.call(x_)),
        with: [f_, g_, x_],
        when: { freeq!([f_, g_], x_) },
        rhs: {
            let f_ = rubi_function_head_symbol(&f_).unwrap();
            let g_ = rubi_function_head_symbol(&g_).unwrap();
            rubi_simp(&((f_.call(x_) / g_.call(x_)).log()), x_)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let f_ = symbols.f_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).cos() * rubi_derivative(Atom::var(n_), Atom::var(f_), x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let f_ = symbols.f_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).sin() * rubi_derivative(Atom::var(n_), Atom::var(f_), x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let f_ = symbols.f_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * capital_f_.pow(a__ + b__ * x_)).pow(p_)
        * rubi_derivative(Atom::var(n_), Atom::var(f_), x_)
}
