use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3213(rules);
    push_rules_rule_3214(rules);
    push_rules_rule_3215(rules);
    push_rules_rule_3216(rules);
    push_rules_rule_3217(rules);
    push_rules_rule_3218(rules);
    push_rules_rule_3219(rules);
    push_rules_rule_3220(rules);
    push_rules_rule_3221(rules);
    push_rules_rule_3222(rules);
    push_rules_rule_3223(rules);
    push_rules_rule_3224(rules);
    push_rules_rule_3225(rules);
    push_rules_rule_3226(rules);
    push_rules_rule_3227(rules);
    push_rules_rule_3228(rules);
    push_rules_rule_3229(rules);
    push_rules_rule_3230(rules);
    push_rules_rule_3231(rules);
    push_rules_rule_3232(rules);
    push_rules_rule_3233(rules);
    push_rules_rule_3234(rules);
    push_rules_rule_3235(rules);
    push_rules_rule_3236(rules);
    push_rules_rule_3237(rules);
    push_rules_rule_3238(rules);
    push_rules_rule_3239(rules);
    push_rules_rule_3240(rules);
    push_rules_rule_3241(rules);
    push_rules_rule_3242(rules);
    push_rules_rule_3243(rules);
    push_rules_rule_3244(rules);
    push_rules_rule_3245(rules);
    push_rules_rule_3246(rules);
    push_rules_rule_3247(rules);
    push_rules_rule_3248(rules);
    push_rules_rule_3249(rules);
    push_rules_rule_3250(rules);
    push_rules_rule_3251(rules);
    push_rules_rule_3252(rules);
    push_rules_rule_3253(rules);
    push_rules_rule_3254(rules);
    push_rules_rule_3255(rules);
    push_rules_rule_3256(rules);
    push_rules_rule_3257(rules);
    push_rules_rule_3258(rules);
    push_rules_rule_3259(rules);
    push_rules_rule_3260(rules);
    push_rules_rule_3261(rules);
    push_rules_rule_3262(rules);
    push_rules_rule_3263(rules);
    push_rules_rule_3264(rules);
    push_rules_rule_3265(rules);
    push_rules_rule_3266(rules);
    push_rules_rule_3267(rules);
    push_rules_rule_3268(rules);
    push_rules_rule_3269(rules);
    push_rules_rule_3270(rules);
    push_rules_rule_3271(rules);
    push_rules_rule_3272(rules);
    push_rules_rule_3273(rules);
    push_rules_rule_3274(rules);
    push_rules_rule_3275(rules);
    push_rules_rule_3276(rules);
    push_rules_rule_3277(rules);
    push_rules_rule_3278(rules);
    push_rules_rule_3279(rules);
    push_rules_rule_3280(rules);
    push_rules_rule_3281(rules);
    push_rules_rule_3282(rules);
    push_rules_rule_3283(rules);
    push_rules_rule_3284(rules);
    push_rules_rule_3285(rules);
    push_rules_rule_3286(rules);
    push_rules_rule_3287(rules);
    push_rules_rule_3288(rules);
    push_rules_rule_3289(rules);
    push_rules_rule_3290(rules);
    push_rules_rule_3291(rules);
    push_rules_rule_3292(rules);
    push_rules_rule_3293(rules);
    push_rules_rule_3294(rules);
    push_rules_rule_3295(rules);
    push_rules_rule_3296(rules);
    push_rules_rule_3297(rules);
    push_rules_rule_3298(rules);
    push_rules_rule_3299(rules);
    push_rules_rule_3300(rules);
    push_rules_rule_3301(rules);
    push_rules_rule_3302(rules);
    push_rules_rule_3303(rules);
    push_rules_rule_3304(rules);
    push_rules_rule_3305(rules);
    push_rules_rule_3306(rules);
    push_rules_rule_3307(rules);
    push_rules_rule_3308(rules);
    push_rules_rule_3309(rules);
    push_rules_rule_3310(rules);
    push_rules_rule_3311(rules);
}

fn push_rules_rule_3213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3213,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (2*a*c+b*d)*x/2 - (b*c+a*d)*Cos[e+f*x]/f - b*d*Cos[e+f*x]*Sin[e+f*x]/(2*f) /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)) * (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&((Atom::num(2) * &a__ * &c__ + &b__ * &d__) * x_ / 2), x_)
                    - rubi_simp(&((&b__ * &c__ + &a__ * &d__) * angle.cos() / &f__), x_)
                    - rubi_simp(&(&b__ * &d__ * angle.cos() * angle.sin() / (Atom::num(2) * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3214,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          b*x/d - (b*c-a*d)/d \\[Star] Int[1/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.551.2"],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)) / (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = Atom::num(1) / (&c__ + &d__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * x_ / &d__), x_)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, recursive)
        },
    ));
}

fn push_rules_rule_3215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3215,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^m*c^m \\[Star] Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && Not[IntegerQ[n] && (LtQ[m,0] && GtQ[n,0] || LtQ[0,n,m] || LtQ[m,n,0])]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
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
            let transformed_integrand =
                angle.cos().pow(Atom::num(2) * &m_) * (&c__ + &d__ * angle.sin()).pow(&n_ - &m_);
            let transformed = rubi_rhs_int(&transformed_integrand, x_);

            rubi_star(a__.pow(&m_) * c__.pow(&m_), transformed)
        },
    ));
}

fn push_rules_rule_3216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3216,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          a*c*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) \\[Star] Int[Cos[e+f*x]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = angle.cos() / (&c__ + &d__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(&a__ * &c__ * angle.cos()
                    / ((&a__ + &b__ * angle.sin()).sqrt()
                        * (&c__ + &d__ * angle.sin()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3217,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && NeQ[n,-1/2]",
        desc: "Doubly degenerate sine recurrence 1a with p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(n_, -Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(-Atom::num(2) * &b__ * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (Atom::num(2) * &n_ + 1) * (&a__ + &b__ * angle.sin()).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3218,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -2*b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(2*n+1)) -
          b*(2*m-1)/(d*(2*n+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IGtQ[m-1/2,0] && LtQ[n,-1] && Not[ILtQ[m+n,0] && GtQ[2*m+n+1,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(&m_ - Atom::num(1) / Atom::num(2), 0)
                && ltq!(n_, -1)
                && !(iltq!(&m_ + &n_, 0) && gtq!(Atom::num(2) * &m_ + &n_ + 1, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * (&c__ + &d__ * angle.sin()).pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ - 1)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (Atom::num(2) * &n_ + 1))), x_)
                    - rubi_star(&b__ * (Atom::num(2) * &m_ - 1)
                            / (&d__ * (Atom::num(2) * &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3219,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) +
          a*(2*m-1)/(m+n) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IGtQ[m-1/2,0] && Not[LtQ[n,-1]] &&
          Not[IGtQ[n-1/2,0] && LtQ[n,m]] && Not[ILtQ[m+n,0] && GtQ[2*m+n+1,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(&m_ - Atom::num(1) / Atom::num(2), 0)
                && !ltq!(n_, -1)
                && !(igtq!(&n_ - Atom::num(1) / Atom::num(2), 0) && ltq!(n_, m_))
                && !(iltq!(&m_ + &n_, 0) && gtq!(Atom::num(2) * &m_ + &n_ + 1, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * (&c__ + &d__ * angle.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ - 1)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (&m_ + &n_))), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &m_ - 1) / (&m_ + &n_), recursive)
        },
    ));
}

fn push_rules_rule_3220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3220,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) \\[Star] Int[1/Cos[e+f*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(&(Atom::num(1) / angle.cos()), x_);

            rubi_star(angle.cos()
                    / ((&a__ + &b__ * angle.sin()).sqrt()
                        * (&c__ + &d__ * angle.sin()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3221,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[m+n+1,0] && NeQ[m,-1/2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ + &n_ + 1, 0)
                && neq!(m_, -Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(&b__ * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3222,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) +
          (m+n+1)/(a*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && ILtQ[Simplify[m+n+1],0] && NeQ[m,-1/2] &&
          (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            let sum = rubi_simplify(&(&m_ + &n_ + 1));
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(sum, 0)
                && neq!(m_, -Atom::num(1) / Atom::num(2))
                && (sum_simplerq!(m_, 1) || !sum_simplerq!(n_, 1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * (&c__ + &d__ * angle.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star((&m_ + &n_ + 1) / (&a__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3223,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) +
          (m+n+1)/(a*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && LtQ[m,-1] && Not[LtQ[m,n,-1]] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && !ltq!(m_, n_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * (&c__ + &d__ * angle.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star((&m_ + &n_ + 1) / (&a__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3224,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/Cos[e+f*x]^(2*FracPart[m]) \\[Star]
            Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && (FractionQ[m] || Not[FractionQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (fractionq!(m_) || !fractionq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                angle.cos().pow(Atom::num(2) * &m_) * (&c__ + &d__ * angle.sin()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(rubi_int_part(&m_))
                    * c__.pow(rubi_int_part(&m_))
                    * (&a__ + &b__ * angle.sin()).pow(&frac_m)
                    * (&c__ + &d__ * angle.sin()).pow(&frac_m)
                    / angle.cos().pow(Atom::num(2) * frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3225,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^2/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b^2*Cos[e+f*x]/(d*f) + 1/d \\[Star] Int[Simp[a^2*d-b*(b*c-2*a*d)*Sin[e+f*x],x]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(2) / (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(a__.pow(2) * &d__ - &b__ * (&b__ * &c__ - Atom::num(2) * &a__ * &d__) * angle.sin(), x_);
            let recursive_integrand = payload / (&c__ + &d__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2) * angle.cos() / (&d__ * &f__)), x_)
                    + rubi_star(Atom::num(1) / &d__, recursive)
        },
    ));
}

fn push_rules_rule_3226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3226,
        source: "Int[1/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*Sin[e+f*x]),x] - d/(b*c-a*d) \\[Star] Int[1/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * i_sin(e__ + f__ * x_)) * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * angle.sin())), x_);
            let recursive2 = rubi_rhs_int(&(Atom::num(1) / (&c__ + &d__ * angle.sin())), x_);

            rubi_star(&b__ / (&b__ * &c__ - &a__ * &d__), recursive1) - rubi_star(&d__ / (&b__ * &c__ - &a__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3227,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          c \\[Star] Int[(b*Sin[e+f*x])^m,x] + d/b \\[Star] Int[(b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{b,c,d,e,f,m},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__, m_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(&b__ * angle.sin()).pow(&m_), x_);
            let recursive2 = rubi_rhs_int(&(&b__ * angle.sin()).pow(&m_ + 1), x_);

            rubi_star(c__, recursive1)
                    + rubi_star(&d__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3228,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && EqQ[a*d*m+b*c*(m+1),0]",
        desc: "Singly degenerate sine recurrence 2c with A\\[Rule]-a d mb (m+1),B\\[Rule]d,n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + 1), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(-&d__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_) / (&f__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3229,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) +
          (a*d*m+b*c*(m+1))/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && LtQ[m,-1/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, (-Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&b__ * &c__ - &a__ * &d__) * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star((&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + 1))
                            / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3230,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) +
          (a*d*m+b*c*(m+1))/(b*(m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, (-Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_) / (&f__ * (&m_ + 1))), x_)
                    + rubi_star((&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + 1))
                            / (&b__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3231,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          (b*c-a*d)/b \\[Star] Int[1/Sqrt[a+b*Sin[e+f*x]],x] + d/b \\[Star] Int[Sqrt[a+b*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [c__, d__, e__, f__, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 =
                rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(&(&a__ + &b__ * angle.sin()).sqrt(), x_);

            rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, recursive1) + rubi_star(&d__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3232,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) +
          1/(m+1) \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && GtQ[m,0] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]a c,B\\[Rule]b c+a d,C\\[Rule]b d,m\\[Rule]0,n\\[Rule]n-1,p\\[Rule]0",
        refs: ["G&R 2.551.1 inverted"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &b__ * &d__ * &m_
                    + &a__ * &c__ * (&m_ + 1)
                    + (&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + 1)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_) / (&f__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&m_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3233,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) +
          1/((m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(b*c-a*d)*(m+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && LtQ[m,-1] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]c,B\\[Rule]d,C\\[Rule]0,n\\[Rule]0,p\\[Rule]0",
        refs: ["G&R 2.551.1"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                (&a__ * &c__ - &b__ * &d__) * (&m_ + 1)
                    - (&b__ * &c__ - &a__ * &d__) * (&m_ + 2) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * payload;
            let determinant = a__.pow(2) - b__.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-(&b__ * &c__ - &a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&f__ * (&m_ + 1) * &determinant)), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * determinant), recursive)
        },
    ));
}

fn push_rules_rule_3234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3234,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          c*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]]) \\[Star] Subst[Int[(a+b*x)^m*Sqrt[1+d/c*x]/Sqrt[1-d/c*x],x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && Not[IntegerQ[2*m]] && EqQ[c^2-d^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(Atom::num(2) * &m_)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_)
                * (Atom::num(1) + &d__ * &z / &c__).sqrt()
                / (Atom::num(1) - &d__ * &z / &c__).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = angle.sin();
            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(&c__ * angle.cos()
                    / (&f__
                        * (Atom::num(1) + angle.sin()).sqrt()
                        * (Atom::num(1) - angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3235,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (b*c-a*d)/b \\[Star] Int[(a+b*Sin[e+f*x])^m,x] + d/b \\[Star] Int[(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(&a__ + &b__ * angle.sin()).pow(&m_), x_);
            let recursive2 = rubi_rhs_int(&(&a__ + &b__ * angle.sin()).pow(&m_ + 1), x_);

            rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, recursive1) + rubi_star(&d__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3236,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          Int[ExpandTrig[(a+b*sin[e+f*x])^m*(d*sin[e+f*x])^n,x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2,0] && IGtQ[m,0] && RationalQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, m_, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
                && rationalq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&d__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3237,
        source: "Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) -
          1/(a^2*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && LtQ[m,-1/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [e__, f__, a__, b__, m_, x_],
        optional: [e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, (-Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&a__ * &m_ - &b__ * (Atom::num(2) * &m_ + 1) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    - rubi_star(Atom::num(1) / (a__.pow(2) * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3238,
        source: "Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) +
          1/(b*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(b*(m+1)-a*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1/2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [e__, f__, a__, b__, m_, x_],
        optional: [e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, (-Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&b__ * (&m_ + 1) - &a__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3239,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])/(a*f*(2*m+1)) +
          1/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*c*d*(m-1)+b*(d^2+c^2*(m+1))+d*(a*d*(m-1)+b*c*(m+2))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && LtQ[m,-1]",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]c,B\\[Rule]d,n\\[Rule]1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &a__ * &c__ * &d__ * (&m_ - 1)
                    + &b__ * (d__.pow(2) + c__.pow(2) * (&m_ + 1))
                    + &d__ * (&a__ * &d__ * (&m_ - 1) + &b__ * &c__ * (&m_ + 2)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&b__ * &c__ - &a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin())
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3240,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) +
          1/(b*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &b__ * (d__.pow(2) * (&m_ + 1) + c__.pow(2) * (&m_ + 2))
                    - &d__ * (&a__ * &d__ - Atom::num(2) * &b__ * &c__ * (&m_ + 2)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-d__.pow(2) * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3241,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b^2*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) +
          b^2/(d*(n+1)*(b*c+a*d)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[a*c*(m-2)-b*d*(m-2*n-4)-(b*c*(m-1)-a*d*(m+2*n+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1] && LtQ[n,-1] &&
          (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 1a with A\\[Rule]a,B\\[Rule]b,m\\[Rule]m-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                    || integerq!(&m_ + Atom::num(1) / Atom::num(2))
                    || integerq!(m_) && eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let denominator = &b__ * &c__ + &a__ * &d__;
            let payload = simp!(
                &a__ * &c__ * (&m_ - 2)
                    - &b__ * &d__ * (&m_ - Atom::num(2) * &n_ - 4)
                    - (&b__ * &c__ * (&m_ - 1) - &a__ * &d__ * (&m_ + Atom::num(2) * &n_ + 1))
                        * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2)
                    * (&b__ * &c__ - &a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&d__ * &f__ * (&n_ + 1) * &denominator)), x_)
                    + rubi_star(b__.pow(2) / (&d__ * (&n_ + 1) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_3242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3242,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) +
          1/(d*(m+n)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
            Simp[a*b*c*(m-2)+b^2*d*(n+1)+a^2*d*(m+n)-b*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,1] && Not[LtQ[n,-1]] &&
          (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && EqQ[c,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 1)
                && !ltq!(n_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                    || integerq!(&m_ + Atom::num(1) / Atom::num(2))
                    || integerq!(m_) && eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &a__ * &b__ * &c__ * (&m_ - 2)
                    + b__.pow(2) * &d__ * (&n_ + 1)
                    + a__.pow(2) * &d__ * (&m_ + &n_)
                    - &b__
                        * (&b__ * &c__ * (&m_ - 1)
                            - &a__ * &d__ * (Atom::num(3) * &m_ + Atom::num(2) * &n_ - 2))
                        * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&d__ * &f__ * (&m_ + &n_))), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3243,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) -
          1/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*Simp[a*d*n-b*c*(m+1)-b*d*(m+n+1)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && LtQ[0,n,1] &&
          (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && ltq!(0, n_, 1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                    || integerq!(m_) && eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &a__ * &d__ * &n_
                    - &b__ * &c__ * (&m_ + 1)
                    - &b__ * &d__ * (&m_ + &n_ + 1) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_) * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    - rubi_star(Atom::num(1) / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3244,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(a*f*(2*m+1)) +
          1/(a*b*(2*m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
            Simp[b*(c^2*(m+1)+d^2*(n-1))+a*c*d*(m-n+1)+d*(a*d*(m-n+1)+b*c*(m+n))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && GtQ[n,1] &&
          (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && gtq!(n_, 1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                    || integerq!(m_) && eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &b__ * (c__.pow(2) * (&m_ + 1) + d__.pow(2) * (&n_ - 1))
                    + &a__ * &c__ * &d__ * (&m_ - &n_ + 1)
                    + &d__ * (&a__ * &d__ * (&m_ - &n_ + 1) + &b__ * &c__ * (&m_ + &n_)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 2)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&b__ * &c__ - &a__ * &d__)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3245,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) +
          1/(a*(2*m+1)*(b*c-a*d)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[b*c*(m+1)-a*d*(2*m+n+2)+b*d*(m+n+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && Not[GtQ[n,0]] &&
          (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && !gtq!(n_, 0)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                    || integerq!(m_) && eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let payload = simp!(
                &b__ * &c__ * (&m_ + 1)
                    - &a__ * &d__ * (Atom::num(2) * &m_ + &n_ + 2)
                    + &b__ * &d__ * (&m_ + &n_ + 2) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(b__.pow(2)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&a__ * &f__ * (Atom::num(2) * &m_ + 1) * &determinant)), x_)
                    + rubi_star(Atom::num(1) / (&a__ * (Atom::num(2) * &m_ + 1) * determinant), recursive)
        },
    ));
}

fn push_rules_rule_3246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3246,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(a*f*(a+b*Sin[e+f*x])) -
          d/(a*b) \\[Star] Int[(c+d*Sin[e+f*x])^(n-2)*Simp[b*d*(n-1)-a*c*n+(b*c*(n-1)-a*d*n)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[n,1] && (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]c,B\\[Rule]d,m\\[Rule]-1,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(n_, 1)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &b__ * &d__ * (&n_ - 1)
                    - &a__ * &c__ * &n_
                    + (&b__ * &c__ * (&n_ - 1) - &a__ * &d__ * &n_) * angle.sin(),
                x_
            );
            let recursive_integrand = (&c__ + &d__ * angle.sin()).pow(&n_ - 2) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-(&b__ * &c__ - &a__ * &d__)
                    * angle.cos()
                    * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                    / (&a__ * &f__ * (&a__ + &b__ * angle.sin()))), x_)
                    - rubi_star(&d__ / (&a__ * &b__), recursive)
        },
    ));
}

fn push_rules_rule_3247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3247,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b^2*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(a*f*(b*c-a*d)*(a+b*Sin[e+f*x])) +
          d/(a*(b*c-a*d)) \\[Star] Int[(c+d*Sin[e+f*x])^n*(a*n-b*(n+1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,0] && (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 2b with A\\[Rule]1,B\\[Rule]0,m\\[Rule]-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, 0)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let recursive_integrand = (&c__ + &d__ * angle.sin()).pow(&n_)
                * (&a__ * &n_ - &b__ * (&n_ + 1) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2) * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&a__ * &f__ * &determinant * (&a__ + &b__ * angle.sin()))), x_)
                    + rubi_star(&d__ / (&a__ * determinant), recursive)
        },
    ));
}

fn push_rules_rule_3248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3248,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(a*f*(a+b*Sin[e+f*x])) +
          d*n/(a*b) \\[Star] Int[(c+d*Sin[e+f*x])^(n-1)*(a-b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && (IntegerQ[2*n] || EqQ[c,0])",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]1,B\\[Rule]0,m\\[Rule]-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && (integerq!(Atom::num(2) * &n_) || eqq!(c__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&c__ + &d__ * angle.sin()).pow(&n_ - 1) * (&a__ - &b__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&a__ * &f__ * (&a__ + &b__ * angle.sin()))), x_)
                    + rubi_star(&d__ * &n_ / (&a__ * &b__), recursive)
        },
    ));
}

fn push_rules_rule_3249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3249,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) +
          2*n*(b*c+a*d)/(b*(2*n+1)) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[n,0] && IntegerQ[2*n]",
        desc: "Singly degenerate sine recurrence 1b with A\\[Rule]c,B\\[Rule]d,m\\[Rule]12,n\\[Rule]n-1,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(n_, 0)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).pow(&n_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &b__ * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (Atom::num(2) * &n_ + 1) * (&a__ + &b__ * angle.sin()).sqrt())), x_)
                    + rubi_star(Atom::num(2) * &n_ * (&b__ * &c__ + &a__ * &d__)
                            / (&b__ * (Atom::num(2) * &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3250,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          -2*b^2*Cos[e+f*x]/(f*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Singly degenerate sine recurrence 1c with A\\[Rule]a,B\\[Rule]b,m\\[Rule]-12,n\\[Rule]-32,p\\[Rule]0",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            / (c__ + d__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(-Atom::num(2) * b__.pow(2) * angle.cos()
                    / (&f__
                        * (&b__ * &c__ + &a__ * &d__)
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&c__ + &d__ * angle.sin()).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3251,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) +
          (2*n+3)*(b*c-a*d)/(2*b*(n+1)*(c^2-d^2)) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,-1] && NeQ[2*n+3,0] && IntegerQ[2*n]",
        desc: "Singly degenerate sine recurrence 1c with A\\[Rule]a,B\\[Rule]b,m\\[Rule]-12,p\\[Rule]0 and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, -1)
                && neq!(Atom::num(2) * &n_ + 3, 0)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let c_square_minus_d_square = c__.pow(2) - d__.pow(2);
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&b__ * &c__ - &a__ * &d__) * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&f__ * (&n_ + 1) * &c_square_minus_d_square * (&a__ + &b__ * angle.sin()).sqrt())), x_)
                    + rubi_star((Atom::num(2) * &n_ + 3) * (&b__ * &c__ - &a__ * &d__)
                            / (Atom::num(2)
                                * &b__
                                * (&n_ + 1)
                                * c_square_minus_d_square), recursive)
        },
    ));
}

fn push_rules_rule_3252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3252,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -2*b/f \\[Star] Subst[Int[1/(b*c+a*d-d*x^2),x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            / (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (&b__ * &c__ + &a__ * &d__ - &d__ * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &b__ * angle.cos() / (&a__ + &b__ * angle.sin()).sqrt();
            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(2) * &b__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3253,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2/f \\[Star] Subst[Int[1/Sqrt[1-x^2/a],x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
        FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2,0] && EqQ[d,a/b]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            / (d__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(d__, &a__ / &b__)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (Atom::num(1) - z.pow(2) / &a__).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &b__ * angle.cos() / (&a__ + &b__ * angle.sin()).sqrt();
            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(2) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3254,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2*b/f \\[Star] Subst[Int[1/(b+d*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (&b__ + &d__ * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &b__ * angle.cos()
                / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt());
            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(2) * &b__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3255,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^2*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]) \\[Star] Subst[Int[(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[IntegerQ[2*n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, e__, f__, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&c__ + &d__ * &z).pow(&n_) / (&a__ - &b__ * &z).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let substituted = rubi_subst(&primitive, sub, angle.sin());

            rubi_star(a__.pow(2) * angle.cos()
                    / (&f__
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&a__ - &b__ * angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3256,
        source: "Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          d/b \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          (b*c-a*d)/b \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [c__, d__, e__, f__, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(&d__ / &b__, recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3257,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2*d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Sin[e+f*x]]) -
          1/(b*(2*n-1)) \\[Star] Int[(c+d*Sin[e+f*x])^(n-2)/Sqrt[a+b*Sin[e+f*x]]*
            Simp[a*c*d-b*(2*d^2*(n-1)+c^2*(2*n-1))+d*(a*d-b*c*(4*n-3))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[n,1] && IntegerQ[2*n]",
        desc: "Singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,m\\[Rule]12,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [c__, d__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &a__ * &c__ * &d__
                    - &b__ * (Atom::num(2) * d__.pow(2) * (&n_ - 1) + c__.pow(2) * (Atom::num(2) * &n_ - 1))
                    + &d__ * (&a__ * &d__ - &b__ * &c__ * (Atom::num(4) * &n_ - 3)) * angle.sin(),
                x_
            );
            let recursive_integrand =
                (&c__ + &d__ * angle.sin()).pow(&n_ - 2) * payload / (&a__ + &b__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &d__ * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                    / (&f__ * (Atom::num(2) * &n_ - 1) * (&a__ + &b__ * angle.sin()).sqrt())), x_)
                    - rubi_star(Atom::num(1) / (&b__ * (Atom::num(2) * &n_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3258,
        source: "Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) -
          1/(2*b*(n+1)*(c^2-d^2)) \\[Star] Int[(c+d*Sin[e+f*x])^(n+1)*Simp[a*d-2*b*c*(n+1)+b*d*(2*n+3)*Sin[e+f*x],x]/Sqrt[a+b*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[n,-1] && IntegerQ[2*n]",
        desc: "Singly degenerate sine recurrence 1c with A\\[Rule]1,B\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [c__, d__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let c_square_minus_d_square = c__.pow(2) - d__.pow(2);
            let payload = simp!(
                &a__ * &d__ - Atom::num(2) * &b__ * &c__ * (&n_ + 1)
                    + &b__ * &d__ * (Atom::num(2) * &n_ + 3) * angle.sin(),
                x_
            );
            let recursive_integrand = (&c__ + &d__ * angle.sin()).pow(&n_ + 1) * payload
                / (&a__ + &b__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * angle.cos() * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&f__ * (&n_ + 1) * &c_square_minus_d_square * (&a__ + &b__ * angle.sin()).sqrt())), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(2)
                                * &b__
                                * (&n_ + 1)
                                * c_square_minus_d_square), recursive)
        },
    ));
}

fn push_rules_rule_3259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3259,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/Sqrt[a+b*Sin[e+f*x]],x] - d/(b*c-a*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let recursive1 =
                rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin())),
                x_,
            );

            rubi_star(&b__ / &determinant, recursive1)
                    - rubi_star(&d__ / determinant, recursive2)
        },
    ));
}

fn push_rules_rule_3260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3260,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -Sqrt[2]/(Sqrt[a]*f) \\[Star] Subst[Int[1/Sqrt[1-x^2],x],x,b*Cos[e+f*x]/(a+b*Sin[e+f*x])] /;
        FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2,0] && EqQ[d,a/b] && GtQ[a,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(d__, &a__ / &b__)
                && gtq!(a__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (Atom::num(1) - z.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &b__ * angle.cos() / (&a__ + &b__ * angle.sin());

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(2).sqrt() / (a__.sqrt() * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3261,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*a/f \\[Star] Subst[Int[1/(2*b^2-(a*c-b*d)*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed =
                Atom::num(1) / (Atom::num(2) * b__.pow(2) - (&a__ * &c__ - &b__ * &d__) * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &b__ * angle.cos()
                / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt());

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(2) * &a__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3262,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(f*(m+n)) +
          1/(b*(m+n)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-2)*
            Simp[d*(a*c*m+b*d*(n-1))+b*c^2*(m+n)+d*(a*d*m+b*c*(m+2*n-1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[n,1] && IntegerQ[n]",
        desc: "Singly degenerate sine recurrence 2c with A\\[Rule]c,B\\[Rule]d,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(n_, 1)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &d__ * (&a__ * &c__ * &m_ + &b__ * &d__ * (&n_ - 1))
                    + &b__ * c__.pow(2) * (&m_ + &n_)
                    + &d__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + Atom::num(2) * &n_ - 1)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 2)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                    / (&f__ * (&m_ + &n_))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3263,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]]) \\[Star] Subst[Int[(1+b/a*x)^(m-1/2)*(c+d*x)^n/Sqrt[1-b/a*x],x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (Atom::num(1) + &b__ * &z / &a__).pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_)
                / (Atom::num(1) - &b__ * &z / &a__).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, angle.sin());

            rubi_star(a__.pow(&m_) * angle.cos()
                    / (&f__
                        * (Atom::num(1) + angle.sin()).sqrt()
                        * (Atom::num(1) - angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3264,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*(d/b)^n*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]) \\[Star]
            Subst[Int[(a-x)^n*(2*a-x)^(m-1/2)/Sqrt[x],x],x,a-b*Sin[e+f*x]] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && GtQ[a,0] && GtQ[d/b,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, m_, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && gtq!(a__, 0)
                && gtq!(&d__ / &b__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed =
                (&a__ - &z).pow(&n_) * (Atom::num(2) * &a__ - &z).pow(&m_ - Atom::num(1) / Atom::num(2))
                    / z.sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = &a__ - &b__ * angle.sin();

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-&b__ * (&d__ / &b__).pow(&n_) * angle.cos()
                    / (&f__
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&a__ - &b__ * angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3265,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          (d/b)^IntPart[n]*(d*Sin[e+f*x])^FracPart[n]/(b*Sin[e+f*x])^FracPart[n] \\[Star] Int[(a+b*Sin[e+f*x])^m*(b*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && GtQ[a,0] && Not[GtQ[d/b,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, m_, d__, n_, x_],
        optional: [b__, e__, f__, d__, n_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && gtq!(a__, 0)
                && !gtq!(&d__ / &b__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_) * (&b__ * angle.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let frac_n = rubi_frac_part(&n_);

            rubi_star((&d__ / &b__).pow(rubi_int_part(&n_))
                    * (&d__ * angle.sin()).pow(&frac_n)
                    / (&b__ * angle.sin()).pow(frac_n), recursive)
        },
    ));
}

fn push_rules_rule_3266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3266,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]/(1+b/a*Sin[e+f*x])^FracPart[m] \\[Star]
            Int[(1+b/a*Sin[e+f*x])^m*(d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && Not[GtQ[a,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, m_, d__, n_, x_],
        optional: [b__, e__, f__, d__, n_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let normalized = Atom::num(1) + &b__ * angle.sin() / &a__;
            let recursive_integrand = normalized.pow(&m_) * (&d__ * angle.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let frac_m = rubi_frac_part(&m_);

            rubi_star(a__.pow(rubi_int_part(&m_))
                    * (&a__ + &b__ * angle.sin()).pow(&frac_m)
                    / normalized.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3267,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^2*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]) \\[Star] Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_)
                / (&a__ - &b__ * &z).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, angle.sin());

            rubi_star(a__.pow(2) * angle.cos()
                    / (&f__
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&a__ - &b__ * angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3268,
        source: "Int[(b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          2*c*d/b \\[Star] Int[(b*Sin[e+f*x])^(m+1),x] + Int[(b*Sin[e+f*x])^m*(c^2+d^2*Sin[e+f*x]^2),x] /;
        FreeQ[{b,c,d,e,f,m},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(2),
        with: [b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__, m_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(&b__ * angle.sin()).pow(&m_ + 1), x_);
            let recursive2 = rubi_rhs_int(
                &((&b__ * angle.sin()).pow(&m_) * (c__.pow(2) + d__.pow(2) * angle.sin().pow(2))),
                x_,
            );

            rubi_star(Atom::num(2) * &c__ * &d__ / &b__, recursive1) + recursive2
        },
    ));
}

fn push_rules_rule_3269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3269,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) -
          1/(b*(m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*
            Simp[b*(m+1)*(2*b*c*d-a*(c^2+d^2))+(a^2*d^2-2*a*b*c*d*(m+2)+b^2*(d^2*(m+1)+c^2*(m+2)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && LtQ[m,-1]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]c2,B\\[Rule]2 c d,C\\[Rule]d2,n\\[Rule]0,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant_square = b__.pow(2) * c__.pow(2)
                - Atom::num(2) * &a__ * &b__ * &c__ * &d__
                + a__.pow(2) * d__.pow(2);
            let a_square_minus_b_square = a__.pow(2) - b__.pow(2);
            let payload = simp!(
                &b__ * (&m_ + 1) * (Atom::num(2) * &b__ * &c__ * &d__ - &a__ * (c__.pow(2) + d__.pow(2)))
                    + (a__.pow(2) * d__.pow(2)
                        - Atom::num(2) * &a__ * &b__ * &c__ * &d__ * (&m_ + 2)
                        + b__.pow(2) * (d__.pow(2) * (&m_ + 1) + c__.pow(2) * (&m_ + 2)))
                        * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-determinant_square * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1) * &a_square_minus_b_square)), x_)
                    - rubi_star(Atom::num(1)
                            / (&b__ * (&m_ + 1) * a_square_minus_b_square), recursive)
        },
    ));
}

fn push_rules_rule_3270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3270,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) +
          1/(b*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = simp!(
                &b__ * (d__.pow(2) * (&m_ + 1) + c__.pow(2) * (&m_ + 2))
                    - &d__ * (&a__ * &d__ - Atom::num(2) * &b__ * &c__ * (&m_ + 2)) * angle.sin(),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-d__.pow(2) * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3271,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) +
          1/(d*(n+1)*(c^2-d^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^(n+1)*
            Simp[b*(m-2)*(b*c-a*d)^2+a*d*(n+1)*(c*(a^2+b^2)-2*a*b*d)+
              (b*(n+1)*(a*b*c^2+c*d*(a^2+b^2)-3*a*b*d^2)-a*(n+2)*(b*c-a*d)^2)*Sin[e+f*x]+
              b*(b^2*(c^2-d^2)-m*(b*c-a*d)^2+d*n*(2*a*b*c-d*(a^2+b^2)))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,2] && LtQ[n,-1] && (IntegerQ[m] || IntegersQ[2*m,2*n])",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]c2,B\\[Rule]2 c d,C\\[Rule]d2,n\\[Rule]n-2,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 2)
                && ltq!(n_, -1)
                && (integerq!(m_) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let determinant = &b__ * &c__ - &a__ * &d__;
            let determinant_square = determinant.pow(2);
            let c_square_minus_d_square = c__.pow(2) - d__.pow(2);
            let payload = simp!(
                &b__ * (&m_ - 2) * &determinant_square
                    + &a__ * &d__ * (&n_ + 1) * (&c__ * (a__.pow(2) + b__.pow(2)) - Atom::num(2) * &a__ * &b__ * &d__)
                    + (&b__ * (&n_ + 1) * (&a__ * &b__ * c__.pow(2) + &c__ * &d__ * (a__.pow(2) + b__.pow(2)) - Atom::num(3) * &a__ * &b__ * d__.pow(2))
                        - &a__ * (&n_ + 2) * &determinant_square)
                        * &sin
                    + &b__
                        * (b__.pow(2) * &c_square_minus_d_square
                            - &m_ * &determinant_square
                            + &d__ * &n_ * (Atom::num(2) * &a__ * &b__ * &c__ - &d__ * (a__.pow(2) + b__.pow(2))))
                        * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 3)
                * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-determinant_square
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&d__ * &f__ * (&n_ + 1) * &c_square_minus_d_square)), x_)
                    + rubi_star(Atom::num(1)
                            / (&d__ * (&n_ + 1) * c_square_minus_d_square), recursive)
        },
    ));
}

fn push_rules_rule_3272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3272,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) +
          1/(d*(m+n)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^n*
            Simp[a^3*d*(m+n)+b^2*(b*c*(m-2)+a*d*(n+1))-
              b*(a*b*c-b^2*d*(m+n-1)-3*a^2*d*(m+n))*Sin[e+f*x]-
              b^2*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[m,2] &&
          (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IGtQ[n,2] && (Not[IntegerQ[m]] || EqQ[a,0] && NeQ[c,0])]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(m_, 2)
                && (integerq!(m_) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
                && !(igtq!(n_, 2) && (!integerq!(m_) || eqq!(a__, 0) && neq!(c__, 0)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let payload = simp!(
                a__.pow(3) * &d__ * (&m_ + &n_)
                    + b__.pow(2) * (&b__ * &c__ * (&m_ - 2) + &a__ * &d__ * (&n_ + 1))
                    - &b__ * (&a__ * &b__ * &c__ - b__.pow(2) * &d__ * (&m_ + &n_ - 1) - Atom::num(3) * a__.pow(2) * &d__ * (&m_ + &n_)) * &sin
                    - b__.pow(2) * (&b__ * &c__ * (&m_ - 1) - &a__ * &d__ * (Atom::num(3) * &m_ + Atom::num(2) * &n_ - 2)) * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 3)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&d__ * &f__ * (&m_ + &n_))), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3273,
        source: "Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          -2*a*d*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) -
          d^2/(a^2-b^2) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(d*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]0,B\\[Rule]d,C\\[Rule]0,m\\[Rule]-32,n\\[Rule]-12,p\\[Rule]0",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant = a__.pow(2) - b__.pow(2);
            let recursive_integrand = (&a__ + &b__ * angle.sin()).sqrt()
                / (&d__ * angle.sin()).pow(Atom::num(3) / Atom::num(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2)
                    * &a__
                    * &d__
                    * angle.cos()
                    / (&f__
                        * &determinant
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&d__ * angle.sin()).sqrt())), x_)
                    - rubi_star(d__.pow(2) / determinant, recursive)
        },
    ));
}

fn push_rules_rule_3274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3274,
        source: "Int[Sqrt[c_+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          (c-d)/(a-b) \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] -
          (b*c-a*d)/(a-b) \\[Star] Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [c__, d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((Atom::num(1) + angle.sin())
                    / ((&a__ + &b__ * angle.sin()).pow(Atom::num(3) / Atom::num(2))
                        * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star((&c__ - &d__) / (&a__ - &b__), recursive1) - rubi_star((&b__ * &c__ - &a__ * &d__) / (&a__ - &b__), recursive2)
        },
    ));
}

fn push_rules_rule_3275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3275,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) +
          1/((m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
            Simp[a*c*(m+1)+b*d*n+(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-b*d*(m+n+2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && LtQ[0,n,1] && IntegersQ[2*m,2*n]",
        desc: "Nondegenerate sine recurrence 1c with A\\[Rule]c,B\\[Rule]d,C\\[Rule]0,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && ltq!(0, n_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let determinant = a__.pow(2) - b__.pow(2);
            let payload = simp!(
                &a__ * &c__ * (&m_ + 1)
                    + &b__ * &d__ * &n_
                    + (&a__ * &d__ * (&m_ + 1) - &b__ * &c__ * (&m_ + 2)) * &sin
                    - &b__ * &d__ * (&m_ + &n_ + 2) * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (&m_ + 1) * &determinant)), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * determinant), recursive)
        },
    ));
}

fn push_rules_rule_3276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3276,
        source: "Int[(d_.*sin[e_.+f_.*x_])^(3/2)/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          d/b \\[Star] Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] -
          a*d/b \\[Star] Int[Sqrt[d*Sin[e+f*x]]/(a+b*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 =
                rubi_rhs_int(&((&d__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&d__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).pow(Atom::num(3) / Atom::num(2))),
                x_,
            );

            rubi_star(&d__ / &b__, recursive1)
                    - rubi_star(&a__ * &d__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3277,
        source: "Int[(c_+d_.*sin[e_.+f_.*x_])^(3/2)/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
          d^2/b^2 \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          (b*c-a*d)/b^2 \\[Star] Int[Simp[b*c+a*d+2*b*d*Sin[e+f*x],x]/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [c__, d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );
            let payload = simp!(&b__ * &c__ + &a__ * &d__ + Atom::num(2) * &b__ * &d__ * angle.sin(), x_);
            let recursive2 = rubi_rhs_int(
                &(payload / ((&a__ + &b__ * angle.sin()).pow(Atom::num(3) / Atom::num(2))
                    * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(d__.pow(2) / b__.pow(2), recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3278,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) +
          1/((m+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
            Simp[c*(a*c-b*d)*(m+1)+d*(b*c-a*d)*(n-1)+(d*(a*c-b*d)*(m+1)-c*(b*c-a*d)*(m+2))*Sin[e+f*x]-d*(b*c-a*d)*(m+n+1)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && LtQ[1,n,2] && IntegersQ[2*m,2*n]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]c,B\\[Rule]d,C\\[Rule]0,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && ltq!(1, n_, 2)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let determinant = a__.pow(2) - b__.pow(2);
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let ac_minus_bd = &a__ * &c__ - &b__ * &d__;
            let payload = simp!(
                &c__ * &ac_minus_bd * (&m_ + 1)
                    + &d__ * &bc_minus_ad * (&n_ - 1)
                    + (&d__ * &ac_minus_bd * (&m_ + 1) - &c__ * &bc_minus_ad * (&m_ + 2)) * &sin
                    - &d__ * &bc_minus_ad * (&m_ + &n_ + 1) * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 2)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&bc_minus_ad
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                    / (&f__ * (&m_ + 1) * &determinant)), x_)
                    + rubi_star(Atom::num(1) / ((&m_ + 1) * determinant), recursive)
        },
    ));
}

fn push_rules_rule_3279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3279,
        source: "Int[1/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2*b*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) +
          d/(a^2-b^2) \\[Star] Int[(b+a*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0]",
        desc: "Nondegenerate sine recurrence 1a with c\\[Rule]0,A\\[Rule]1,B\\[Rule]0,C\\[Rule]0,p\\[Rule]0,m\\[Rule]-32,n\\[Rule]-12",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let determinant = a__.pow(2) - b__.pow(2);
            let recursive_integrand = (&b__ + &a__ * angle.sin())
                / ((&a__ + &b__ * angle.sin()).sqrt() * (&d__ * angle.sin()).pow(Atom::num(3) / Atom::num(2)));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(2) * &b__ * angle.cos()
                    / (&f__
                        * &determinant
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&d__ * angle.sin()).sqrt())), x_)
                    + rubi_star(&d__ / determinant, recursive)
        },
    ));
}

fn push_rules_rule_3280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3280,
        source: "Int[1/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          1/(a-b) \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] -
          b/(a-b) \\[Star] Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((Atom::num(1) + angle.sin())
                    / ((&a__ + &b__ * angle.sin()).pow(Atom::num(3) / Atom::num(2))
                        * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(Atom::num(1) / (&a__ - &b__), recursive1)
                    - rubi_star(&b__ / (&a__ - &b__), recursive2)
        },
    ));
}

fn push_rules_rule_3281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3281,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) +
          1/((m+1)*(b*c-a*d)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
            Simp[a*(b*c-a*d)*(m+1)+b^2*d*(m+n+2)-(b^2*c+b*(b*c-a*d)*(m+1))*Sin[e+f*x]-b^2*d*(m+n+3)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[m,-1] && IntegersQ[2*m,2*n] &&
          (EqQ[a,0] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && LtQ[n,-1] && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a,0])])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && (eqq!(a__, 0) && integerq!(m_) && !integerq!(n_)
                    || !(integerq!(Atom::num(2) * &n_)
                        && ltq!(n_, -1)
                        && (integerq!(n_) && !integerq!(m_) || eqq!(a__, 0))))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let a_square_minus_b_square = a__.pow(2) - b__.pow(2);
            let payload = simp!(
                &a__ * &bc_minus_ad * (&m_ + 1)
                    + b__.pow(2) * &d__ * (&m_ + &n_ + 2)
                    - (b__.pow(2) * &c__ + &b__ * &bc_minus_ad * (&m_ + 1)) * &sin
                    - b__.pow(2) * &d__ * (&m_ + &n_ + 3) * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-b__.pow(2)
                    * angle.cos()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)
                    / (&f__ * (&m_ + 1) * &bc_minus_ad * &a_square_minus_b_square)), x_)
                    + rubi_star(Atom::num(1)
                            / ((&m_ + 1) * bc_minus_ad * a_square_minus_b_square), recursive)
        },
    ));
}

fn push_rules_rule_3282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3282,
        source: "Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          d/b \\[Star] Int[1/Sqrt[c+d*Sin[e+f*x]],x] +
          (b*c-a*d)/b \\[Star] Int[1/((a+b*Sin[e+f*x])*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [c__, d__, e__, f__, a__, b__, x_],
        optional: [c__, d__, e__, f__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(Atom::num(1) / (&c__ + &d__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1) / ((&a__ + &b__ * angle.sin()) * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(&d__ / &b__, recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3283,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^(3/2)/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          b/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]],x] - (b*c-a*d)/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            / (c__ + d__ * i_sin(e__ + f__ * x_)),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(&(&a__ + &b__ * angle.sin()).sqrt(), x_);
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin())),
                x_,
            );

            rubi_star(&b__ / &d__, recursive1)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3284,
        source: "Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2/(f*(a+b)*Sqrt[c+d])*EllipticPi[2*b/(a+b),1/2*(e-Pi/2+f*x),2*d/(c+d)] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[c+d,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(&c__ + &d__, 0)
        },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(Atom::num(2)
                    * rubi_elliptic_pi(
                        Atom::num(2) * &b__ / (&a__ + &b__),
                        (angle - pi / Atom::num(2)) / Atom::num(2),
                        Atom::num(2) * &d__ / (&c__ + &d__),
                    )
                    / (&f__ * (&a__ + &b__) * (&c__ + &d__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3285,
        source: "Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2/(f*(a-b)*Sqrt[c-d])*EllipticPi[-2*b/(a-b),1/2*(e+Pi/2+f*x),-2*d/(c-d)] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && GtQ[c-d,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && gtq!(&c__ - &d__, 0)
        },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(Atom::num(2)
                    * rubi_elliptic_pi(
                        -Atom::num(2) * &b__ / (&a__ - &b__),
                        (angle + pi / Atom::num(2)) / Atom::num(2),
                        -Atom::num(2) * &d__ / (&c__ - &d__),
                    )
                    / (&f__ * (&a__ - &b__) * (&c__ - &d__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3286,
        source: "Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[(c+d*Sin[e+f*x])/(c+d)]/Sqrt[c+d*Sin[e+f*x]] \\[Star] Int[1/((a+b*Sin[e+f*x])*Sqrt[c/(c+d)+d/(c+d)*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && Not[GtQ[c+d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && !gtq!(&c__ + &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = Atom::num(1)
                / ((&a__ + &b__ * angle.sin()) * (&c__ / (&c__ + &d__) + &d__ * angle.sin() / (&c__ + &d__)).sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(((&c__ + &d__ * angle.sin()) / (&c__ + &d__)).sqrt()
                    / (&c__ + &d__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3287,
        source: "Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          2*c*Rt[b*(c+d),2]*Tan[e+f*x]*Sqrt[1+Csc[e+f*x]]*Sqrt[1-Csc[e+f*x]]/(d*f*Sqrt[c^2-d^2])*
            EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[c^2-d^2,0] && PosQ[(c+d)/b] && GtQ[c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(c__.pow(2) - d__.pow(2), 0)
                && posq!((&c__ + &d__) / &b__)
                && gtq!(c__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let csc = angle.csc();

            rubi_simp(&(Atom::num(2)
                    * &c__
                    * rubi_rt(&(&b__ * (&c__ + &d__)), 2)
                    * angle.tan()
                    * (Atom::num(1) + &csc).sqrt()
                    * (Atom::num(1) - &csc).sqrt()
                    * rubi_elliptic_pi(
                        (&c__ + &d__) / &d__,
                        ((&c__ + &d__ * &sin).sqrt() / ((&b__ * &sin).sqrt() * rubi_rt(&((&c__ + &d__) / &b__), 2))).asin(),
                        -(&c__ + &d__) / (&c__ - &d__),
                    )
                    / (&d__ * &f__ * (c__.pow(2) - d__.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3288,
        source: "Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          2*b*Tan[e+f*x]/(d*f)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
            EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
        FreeQ[{b,c,d,e,f},x] && NeQ[c^2-d^2,0] && PosQ[(c+d)/b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && posq!((&c__ + &d__) / &b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let csc = angle.csc();

            rubi_simp(&(Atom::num(2)
                    * &b__
                    * angle.tan()
                    * rubi_rt(&((&c__ + &d__) / &b__), 2)
                    * (&c__ * (Atom::num(1) + &csc) / (&c__ - &d__)).sqrt()
                    * (&c__ * (Atom::num(1) - &csc) / (&c__ + &d__)).sqrt()
                    * rubi_elliptic_pi(
                        (&c__ + &d__) / &d__,
                        ((&c__ + &d__ * &sin).sqrt() / ((&b__ * &sin).sqrt() * rubi_rt(&((&c__ + &d__) / &b__), 2))).asin(),
                        -(&c__ + &d__) / (&c__ - &d__),
                    )
                    / (&d__ * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3289,
        source: "Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          Sqrt[b*Sin[e+f*x]]/Sqrt[-b*Sin[e+f*x]] \\[Star] Int[Sqrt[-b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] /;
        FreeQ[{b,c,d,e,f},x] && NeQ[c^2-d^2,0] && NegQ[(c+d)/b]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && negq!((&c__ + &d__) / &b__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (-&b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&b__ * angle.sin()).sqrt() / (-&b__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3290,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          2*(a+b*Sin[e+f*x])/(d*f*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
            Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
            Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
            EllipticPi[b*(c+d)/(d*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && PosQ[(a+b)/(c+d)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && posq!((&a__ + &b__) / (&c__ + &d__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let first = &a__ + &b__ * &sin;
            let second = &c__ + &d__ * &sin;
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let rt = rubi_rt(&((&a__ + &b__) / (&c__ + &d__)), 2);

            rubi_simp(&(Atom::num(2)
                    * &first
                    * (&bc_minus_ad * (Atom::num(1) + &sin) / ((&c__ - &d__) * &first)).sqrt()
                    * (-&bc_minus_ad * (Atom::num(1) - &sin) / ((&c__ + &d__) * &first)).sqrt()
                    * rubi_elliptic_pi(
                        &b__ * (&c__ + &d__) / (&d__ * (&a__ + &b__)),
                        (&rt * second.sqrt() / first.sqrt()).asin(),
                        (&a__ - &b__) * (&c__ + &d__) / ((&a__ + &b__) * (&c__ - &d__)),
                    )
                    / (&d__ * &f__ * rt * angle.cos())), x_)
        },
    ));
}

fn push_rules_rule_3291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3291,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]] \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[-c-d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && NegQ[(a+b)/(c+d)]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && negq!((&a__ + &b__) / (&c__ + &d__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).sqrt() / (-&c__ - &d__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((-&c__ - &d__ * angle.sin()).sqrt()
                    / (&c__ + &d__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3292,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*d/(f*Sqrt[a+b*d])*EllipticF[ArcSin[Cos[e+f*x]/(1+d*Sin[e+f*x])],-(a-b*d)/(a+b*d)] /;
        FreeQ[{a,b,d,e,f},x] && LtQ[a^2-b^2,0] && EqQ[d^2,1] && GtQ[b*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && ltq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(d__.pow(2), 1)
                && gtq!(&b__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(-Atom::num(2)
                    * &d__
                    * rubi_elliptic_f(
                        (angle.cos() / (Atom::num(1) + &d__ * angle.sin())).asin(),
                        -(&a__ - &b__ * &d__) / (&a__ + &b__ * &d__),
                    )
                    / (&f__ * (&a__ + &b__ * &d__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3293,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[Sign[b]*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]] \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[Sign[b]*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,d,e,f},x] && LtQ[a^2-b^2,0] && GtQ[b^2,0] && Not[EqQ[d^2,1] && GtQ[b*d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && ltq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(b__.pow(2), 0)
                && !(eqq!(d__.pow(2), 1) && gtq!(&b__ * &d__, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sign_b = rubi_sign(&b__);
            let recursive_integrand =
                Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (&sign_b * angle.sin()).sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&sign_b * angle.sin()).sqrt() / (&d__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3294,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*Sqrt[a^2]*Sqrt[-Cot[e+f*x]^2]/(a*f*Sqrt[a^2-b^2]*Cot[e+f*x])*Rt[(a+b)/d,2]*
            EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
        FreeQ[{a,b,d,e,f},x] && GtQ[a^2-b^2,0] && PosQ[(a+b)/d] && GtQ[a^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && gtq!(a__.pow(2) - b__.pow(2), 0)
                && posq!((&a__ + &b__) / &d__)
                && gtq!(a__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let rt = rubi_rt(&((&a__ + &b__) / &d__), 2);

            rubi_simp(&(-Atom::num(2)
                    * a__.pow(2).sqrt()
                    * (-angle.cot().pow(2)).sqrt()
                    * &rt
                    * rubi_elliptic_f(
                        ((&a__ + &b__ * angle.sin()).sqrt() / ((&d__ * angle.sin()).sqrt() * &rt)).asin(),
                        -(&a__ + &b__) / (&a__ - &b__),
                    )
                    / (&a__ * &f__ * (a__.pow(2) - b__.pow(2)).sqrt() * angle.cot())), x_)
        },
    ));
}

fn push_rules_rule_3295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3295,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*Tan[e+f*x]/(a*f)*Rt[(a+b)/d,2]*Sqrt[a*(1-Csc[e+f*x])/(a+b)]*Sqrt[a*(1+Csc[e+f*x])/(a-b)]*
            EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0] && PosQ[(a+b)/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && posq!((&a__ + &b__) / &d__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let rt = rubi_rt(&((&a__ + &b__) / &d__), 2);
            let csc = angle.csc();

            rubi_simp(&(-Atom::num(2)
                    * angle.tan()
                    * &rt
                    * (&a__ * (Atom::num(1) - &csc) / (&a__ + &b__)).sqrt()
                    * (&a__ * (Atom::num(1) + &csc) / (&a__ - &b__)).sqrt()
                    * rubi_elliptic_f(
                        ((&a__ + &b__ * angle.sin()).sqrt() / ((&d__ * angle.sin()).sqrt() * &rt)).asin(),
                        -(&a__ + &b__) / (&a__ - &b__),
                    )
                    / (&a__ * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3296,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[-d*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]] \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[-d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0] && NegQ[(a+b)/d]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && negq!((&a__ + &b__) / &d__)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (-&d__ * angle.sin()).sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((-&d__ * angle.sin()).sqrt() / (&d__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3297,
        source: "Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2*(c+d*Sin[e+f*x])/(f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Cos[e+f*x])*
            Sqrt[(b*c-a*d)*(1-Sin[e+f*x])/((a+b)*(c+d*Sin[e+f*x]))]*
            Sqrt[-(b*c-a*d)*(1+Sin[e+f*x])/((a-b)*(c+d*Sin[e+f*x]))]*
            EllipticF[ArcSin[Rt[(c+d)/(a+b),2]*(Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]])],(a+b)*(c-d)/((a-b)*(c+d))] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && PosQ[(c+d)/(a+b)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && posq!((&c__ + &d__) / (&a__ + &b__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let first = &a__ + &b__ * &sin;
            let second = &c__ + &d__ * &sin;
            let bc_minus_ad = &b__ * &c__ - &a__ * &d__;
            let rt = rubi_rt(&((&c__ + &d__) / (&a__ + &b__)), 2);

            rubi_simp(&(Atom::num(2)
                    * &second
                    * (&bc_minus_ad * (Atom::num(1) - &sin) / ((&a__ + &b__) * &second)).sqrt()
                    * (-&bc_minus_ad * (Atom::num(1) + &sin) / ((&a__ - &b__) * &second)).sqrt()
                    * rubi_elliptic_f(
                        (&rt * first.sqrt() / second.sqrt()).asin(),
                        (&a__ + &b__) * (&c__ - &d__) / ((&a__ - &b__) * (&c__ + &d__)),
                    )
                    / (&f__ * &bc_minus_ad * rt * angle.cos())), x_)
        },
    ));
}

fn push_rules_rule_3298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3298,
        source: "Int[1/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[-a-b*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]] \\[Star] Int[1/(Sqrt[-a-b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && NegQ[(c+d)/(a+b)]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [a__, b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && negq!((&c__ + &d__) / (&a__ + &b__))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                Atom::num(1) / ((-&a__ - &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((-&a__ - &b__ * angle.sin()).sqrt()
                    / (&a__ + &b__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3299,
        source: "Int[(d_.*sin[e_.+f_.*x_])^(3/2)/Sqrt[a_.+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -a*d/(2*b) \\[Star] Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] +
          d/(2*b) \\[Star] Int[Sqrt[d*Sin[e+f*x]]*(a+2*b*Sin[e+f*x])/Sqrt[a+b*Sin[e+f*x]],x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, a__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 =
                rubi_rhs_int(&((&d__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).sqrt()), x_);
            let recursive2 = rubi_rhs_int(
                &((&d__ * angle.sin()).sqrt() * (&a__ + Atom::num(2) * &b__ * angle.sin())
                    / (&a__ + &b__ * angle.sin()).sqrt()),
                x_,
            );

            rubi_star(-&a__ * &d__ / (Atom::num(2) * &b__), recursive1) + rubi_star(&d__ / (Atom::num(2) * &b__), recursive2)
        },
    ));
}

fn push_rules_rule_3300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3300,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) +
          1/(d*(m+n)) \\[Star] Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n-1)*
            Simp[a^2*c*d*(m+n)+b*d*(b*c*(m-1)+a*d*n)+
              (a*d*(2*b*c+a*d)*(m+n)-b*d*(a*c-b*d*(m+n-1)))*Sin[e+f*x]+
              b*d*(b*c*n+a*d*(2*m+n-1))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && LtQ[0,m,2] && LtQ[-1,n,2] && NeQ[m+n,0] &&
          (IntegerQ[m] || IntegersQ[2*m,2*n])",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]a c,B\\[Rule]b c+a d,C\\[Rule]b d,m\\[Rule]m-1,n\\[Rule]n-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && ltq!(0, m_, 2)
                && ltq!(-1, n_, 2)
                && neq!(&m_ + &n_, 0)
                && (integerq!(m_) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let payload = simp!(
                a__.pow(2) * &c__ * &d__ * (&m_ + &n_)
                    + &b__ * &d__ * (&b__ * &c__ * (&m_ - 1) + &a__ * &d__ * &n_)
                    + (&a__ * &d__ * (Atom::num(2) * &b__ * &c__ + &a__ * &d__) * (&m_ + &n_)
                        - &b__ * &d__ * (&a__ * &c__ - &b__ * &d__ * (&m_ + &n_ - 1)))
                        * &sin
                    + &b__ * &d__ * (&b__ * &c__ * &n_ + &a__ * &d__ * (Atom::num(2) * &m_ + &n_ - 1)) * sin.pow(2),
                x_
            );
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ - 2)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&f__ * (&m_ + &n_))), x_)
                    + rubi_star(Atom::num(1) / (&d__ * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3301,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b/d \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] -
          (b*c-a*d)/d \\[Star] Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_ - 1) * (&c__ + &d__ * angle.sin()).pow(&n_ + 1)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_ - 1) * (&c__ + &d__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star(&b__ / &d__, recursive1)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3302,
        source: "Int[(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a \\[Star] Int[(d*Sin[e+f*x])^n/(a^2-b^2*Sin[e+f*x]^2),x] -
          b/d \\[Star] Int[(d*Sin[e+f*x])^(n+1)/(a^2-b^2*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).pow(n_) / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [d__, e__, f__, n_, a__, b__, x_],
        optional: [d__, e__, f__, n_, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let denominator = a__.pow(2) - b__.pow(2) * angle.sin().pow(2);
            let recursive1 = rubi_rhs_int(&((&d__ * angle.sin()).pow(&n_) / &denominator), x_);
            let recursive2 = rubi_rhs_int(&((&d__ * angle.sin()).pow(&n_ + 1) / denominator), x_);

            rubi_star(a__, recursive1)
                    - rubi_star(&b__ / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3303,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          Int[ExpandTrig[(d*sin[e+f*x])^n*(a-b*sin[e+f*x])^(-m)/(a^2-b^2*sin[e+f*x]^2)^(-m),x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2,0] && ILtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, m_, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&d__ * i_sin(&angle)).pow(&n_)
                * (&a__ - &b__ * i_sin(&angle)).pow(-&m_)
                / (a__.pow(2) - b__.pow(2) * i_sin(&angle).pow(2)).pow(-&m_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3304,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Unintegrable[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [a__, b__, e__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            rubi_unintegrable(
                (&a__ + &b__ * angle.sin()).pow(&m_) * (&c__ + &d__ * angle.sin()).pow(&n_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3305,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.*(d_.*sin[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
          c^IntPart[n]*(c*(d*Sin[e + f*x])^p)^FracPart[n]/(d*Sin[e + f*x])^(p*FracPart[n]) \\[Star]
            Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n*p),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ * (d__ * i_sin(e__ + f__ * x_)).pow(p_)).pow(n_),
        with: [a__, b__, e__, f__, m_, c__, d__, p_, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_n = rubi_frac_part(&n_);
            let int_n = rubi_int_part(&n_);
            let recursive_integrand =
                (&a__ + &b__ * angle.sin()).pow(&m_) * (&d__ * angle.sin()).pow(&n_ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(int_n)
                    * (&c__ * (&d__ * angle.sin()).pow(&p_)).pow(&frac_n)
                    / (&d__ * angle.sin()).pow(&p_ * frac_n), recursive)
        },
    ));
}

fn push_rules_rule_3306(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3306,
        source: "Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.*(d_.*cos[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
          c^IntPart[n]*(c*(d*Cos[e + f*x])^p)^FracPart[n]/(d*Cos[e + f*x])^(p*FracPart[n]) \\[Star]
            Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n*p),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_) * (c__ * (d__ * i_cos(e__ + f__ * x_)).pow(p_)).pow(n_),
        with: [a__, b__, e__, f__, m_, c__, d__, p_, n_, x_],
        optional: [a__, b__, e__, f__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_n = rubi_frac_part(&n_);
            let int_n = rubi_int_part(&n_);
            let recursive_integrand =
                (&a__ + &b__ * angle.cos()).pow(&m_) * (&d__ * angle.cos()).pow(&n_ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(int_n)
                    * (&c__ * (&d__ * angle.cos()).pow(&p_)).pow(&frac_n)
                    / (&d__ * angle.cos()).pow(&p_ * frac_n), recursive)
        },
    ));
}

fn push_rules_rule_3307(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3307,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^n,x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_) * (&d__ + &c__ * angle.sin()).pow(&n_) / angle.sin().pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3308(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3308,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^m,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && !integerq!(n_)
                && integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&b__ + &a__ * angle.csc()).pow(&m_) * (&c__ + &d__ * angle.csc()).pow(&n_) / angle.csc().pow(&m_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3309(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3309,
        source: "Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[(b+a*Sec[e+f*x])^m*(c+d*Sec[e+f*x])^n/Sec[e+f*x]^m,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && !integerq!(n_)
                && integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&b__ + &a__ * angle.sec()).pow(&m_) * (&c__ + &d__ * angle.sec()).pow(&n_) / angle.sec().pow(&m_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3310,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          Sin[e+f*x]^n*(c+d*Csc[e+f*x])^n/(d+c*Sin[e+f*x])^n \\[Star] Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && !integerq!(n_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_) * (&d__ + &c__ * angle.sin()).pow(&n_) / angle.sin().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.sin().pow(&n_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)
                    / (&d__ + &c__ * angle.sin()).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3311,
        source: "Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          Cos[e+f*x]^n*(c+d*Sec[e+f*x])^n/(d+c*Cos[e+f*x])^n \\[Star] Int[(a+b*Cos[e+f*x])^m*(d+c*Cos[e+f*x])^n/Cos[e+f*x]^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && !integerq!(n_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.cos()).pow(&m_) * (&d__ + &c__ * angle.cos()).pow(&n_) / angle.cos().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.cos().pow(&n_)
                    * (&c__ + &d__ * angle.sec()).pow(&n_)
                    / (&d__ + &c__ * angle.cos()).pow(&n_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3213_through_3242_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3213..=3242).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3213..=3242).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3243_through_3292_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3243..=3292).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3243..=3292).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3293_through_3311_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3293..=3311).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3293..=3311).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sec(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() / (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (b__ * i_sin(e__ + f__ * x_)).sqrt() / (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_) / (a__ + b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_) / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((a__ + b__ * i_sin(e__ + f__ * x_)) * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_).pow(2) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}
