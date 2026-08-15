use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3725(rules);
    push_rules_rule_3726(rules);
    push_rules_rule_3727(rules);
    push_rules_rule_3728(rules);
    push_rules_rule_3729(rules);
    push_rules_rule_3730(rules);
    push_rules_rule_3731(rules);
    push_rules_rule_3732(rules);
    push_rules_rule_3733(rules);
    push_rules_rule_3734(rules);
    push_rules_rule_3735(rules);
    push_rules_rule_3736(rules);
    push_rules_rule_3737(rules);
    push_rules_rule_3738(rules);
    push_rules_rule_3739(rules);
    push_rules_rule_3740(rules);
    push_rules_rule_3741(rules);
    push_rules_rule_3742(rules);
    push_rules_rule_3743(rules);
    push_rules_rule_3744(rules);
    push_rules_rule_3745(rules);
    push_rules_rule_3746(rules);
    push_rules_rule_3747(rules);
    push_rules_rule_3748(rules);
    push_rules_rule_3749(rules);
    push_rules_rule_3750(rules);
    push_rules_rule_3751(rules);
    push_rules_rule_3752(rules);
    push_rules_rule_3753(rules);
    push_rules_rule_3754(rules);
    push_rules_rule_3755(rules);
    push_rules_rule_3756(rules);
    push_rules_rule_3757(rules);
    push_rules_rule_3758(rules);
    push_rules_rule_3759(rules);
    push_rules_rule_3760(rules);
    push_rules_rule_3761(rules);
    push_rules_rule_3762(rules);
    push_rules_rule_3763(rules);
    push_rules_rule_3764(rules);
    push_rules_rule_3765(rules);
    push_rules_rule_3766(rules);
    push_rules_rule_3767(rules);
    push_rules_rule_3768(rules);
    push_rules_rule_3769(rules);
    push_rules_rule_3770(rules);
    push_rules_rule_3771(rules);
    push_rules_rule_3772(rules);
    push_rules_rule_3773(rules);
    push_rules_rule_3774(rules);
    push_rules_rule_3775(rules);
    push_rules_rule_3776(rules);
}

fn push_rules_rule_3725(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3725,
        source: "Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let recursive_integrand = (&b__ + Atom::num(2) * &c__ * sin.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3726(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3726,
        source: "Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let recursive_integrand = (&b__ + Atom::num(2) * &c__ * cos.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3727,
        source: "Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p) \\[Star] Int[u*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let trinomial = &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * sin.pow(&n_);
            let recursive = rubi_rhs_int(
                &(Atom::var(symbol!("u")) * factor.pow(Atom::num(2) * &p_)),
                x_,
            );

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3728,
        source: "Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p) \\[Star] Int[u*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let trinomial = &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * cos.pow(&n_);
            let recursive = rubi_rhs_int(
                &(Atom::var(symbol!("u")) * factor.pow(Atom::num(2) * &p_)),
                x_,
            );

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 3729,
        source: "Int[1/(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.),x_Symbol] :=
          Module[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[1/(b-q+2*c*Sin[d+e*x]^n),x] -
          2*c/q \\[Star] Int[1/(b+q+2*c*Sin[d+e*x]^n),x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_)
                + c__ * i_sin(d__ + e__ * x_).pow(n2_)),
        with: [a__, b__, c__, d__, e__, n_, n2_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand =
                Atom::num(1) / (&b__ - &q + Atom::num(2) * &c__ * sin.pow(&n_));
            let second_integrand =
                Atom::num(1) / (&b__ + &q + Atom::num(2) * &c__ * sin.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &c__ / &q, first)
                    - rubi_star(Atom::num(2) * &c__ / q, second)
        },
    ));
}

fn push_rules_rule_3730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 3730,
        source: "Int[1/(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.),x_Symbol] :=
          Module[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[1/(b-q+2*c*Cos[d+e*x]^n),x] -
          2*c/q \\[Star] Int[1/(b+q+2*c*Cos[d+e*x]^n),x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_)
                + c__ * i_cos(d__ + e__ * x_).pow(n2_)),
        with: [a__, b__, c__, d__, e__, n_, n2_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand =
                Atom::num(1) / (&b__ - &q + Atom::num(2) * &c__ * cos.pow(&n_));
            let second_integrand =
                Atom::num(1) / (&b__ + &q + Atom::num(2) * &c__ * cos.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &c__ / &q, first)
                    - rubi_star(Atom::num(2) * &c__ / q, second)
        },
    ));
}

fn push_rules_rule_3731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3731,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let recursive_integrand =
                sin.pow(&m_) * (&b__ + Atom::num(2) * &c__ * sin.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3732,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let recursive_integrand =
                cos.pow(&m_) * (&b__ + Atom::num(2) * &c__ * cos.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3733,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p) \\[Star] Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let trinomial = &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * sin.pow(&n_);
            let recursive_integrand = sin.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3734,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p) \\[Star] Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let trinomial = &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * cos.pow(&n_);
            let recursive_integrand = cos.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3735,
        source: "Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f/e \\[Star] Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ + 1);
            let transformed = expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3736,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f/e \\[Star] Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ + 1);
            let transformed = expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3737,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IntegersQ[m,n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = i_sin(&angle);
            let payload = sin.pow(&m_)
                * (&a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3738,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IntegersQ[m,n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = i_cos(&angle);
            let payload = cos.pow(&m_)
                * (&a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3739,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*sin[d_.+e_.*x_])^n_.+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Sin[d+e*x],x]},
          g/e \\[Star] Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Sin[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2,2*n] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_sin(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_sin(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, f__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let g = rubi_free_factors(&sin, x_);
            let transformed = (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&g / &e__, rubi_subst(&primitive, sub, sin / &g))
        },
    ));
}

fn push_rules_rule_3740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3740,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*cos[d_.+e_.*x_])^n_.+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Cos[d+e*x],x]},
          -g/e \\[Star] Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Cos[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2,2*n] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sin(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_cos(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_cos(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, f__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let g = rubi_free_factors(&cos, x_);
            let transformed = (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&g / &e__, rubi_subst(&primitive, sub, cos / &g))
        },
    ));
}

fn push_rules_rule_3741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3741,
        source: "Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                cos.pow(&m_) * (&b__ + Atom::num(2) * &c__ * sin.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3742,
        source: "Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                sin.pow(&m_) * (&b__ + Atom::num(2) * &c__ * cos.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3743,
        source: "Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p) \\[Star] Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let trinomial = &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * sin.pow(&n_);
            let recursive_integrand = cos.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3744,
        source: "Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p) \\[Star] Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let trinomial = &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * cos.pow(&n_);
            let recursive_integrand = sin.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3745,
        source: "Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3746,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3747,
        source: "Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let sin = (&d__ + &e__ * x_).sin();
            let trinomial =
                &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let payload = (Atom::num(1) - sin.pow(2)).pow(&m_ / 2) * trinomial.pow(&p_);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3748,
        source: "Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let cos = (&d__ + &e__ * x_).cos();
            let trinomial =
                &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let payload = (Atom::num(1) - cos.pow(2)).pow(&m_ / 2) * trinomial.pow(&p_);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3749,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Sin[d+e*x],x]},
          g^(m+1)/e \\[Star] Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Sin[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[(m-1)/2] && IntegerQ[2*p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_sin(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_sin(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, f__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let g = rubi_free_factors(&sin, x_);
            let transformed = z.pow(&m_)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_)
                / (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(g.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, sin / &g))
        },
    ));
}

fn push_rules_rule_3750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3750,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Cos[d+e*x],x]},
          -g^(m+1)/e \\[Star] Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Cos[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[(m-1)/2] && IntegerQ[2*p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cot(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_cos(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_cos(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, f__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let g = rubi_free_factors(&cos, x_);
            let transformed = z.pow(&m_)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_)
                / (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-g.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, cos / &g))
        },
    ));
}

fn push_rules_rule_3751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3751,
        source: "Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let recursive_integrand =
                tan.pow(&m_) * (&b__ + Atom::num(2) * &c__ * sin.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3752,
        source: "Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let cot = angle.cot();
            let recursive_integrand =
                cot.pow(&m_) * (&b__ + Atom::num(2) * &c__ * cos.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3753,
        source: "Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p) \\[Star] Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let trinomial = &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * sin.pow(&n_);
            let recursive_integrand = tan.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3754,
        source: "Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p) \\[Star] Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let cot = angle.cot();
            let trinomial = &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * cos.pow(&n_);
            let recursive_integrand = cot.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3755,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * z.pow(Atom::num(2) * &n_)
                    + &b__ * z.pow(&n_) * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3756,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && NeQ[b^2-4*a*c,0] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * z.pow(Atom::num(2) * &n_)
                    + &b__ * z.pow(&n_) * (Atom::num(1) + z.pow(2)).pow(&n_ / 2)
                    + &a__ * (Atom::num(1) + z.pow(2)).pow(&n_)),
                sub,
            );
            let denominator = (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3757,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/(1-sin[d+e*x]^2)^(m/2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let sin = (&d__ + &e__ * x_).sin();
            let trinomial =
                &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let payload = sin.pow(&m_) * trinomial.pow(&p_)
                / (Atom::num(1) - sin.pow(2)).pow(&m_ / 2);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3758,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/(1-cos[d+e*x]^2)^(m/2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let cos = (&d__ + &e__ * x_).cos();
            let trinomial =
                &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let payload = cos.pow(&m_) * trinomial.pow(&p_)
                / (Atom::num(1) - cos.pow(2)).pow(&m_ / 2);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3759,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Sin[d+e*x],x]},
          g^(m+1)/e \\[Star] Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Sin[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[(m-1)/2] && IntegerQ[2*p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cot(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_sin(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_sin(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, f__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let g = rubi_free_factors(&sin, x_);
            let transformed = (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_)
                / z.pow(&m_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(g.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, sin / &g))
        },
    ));
}

fn push_rules_rule_3760(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3760,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
          Module[{g=FreeFactors[Cos[d+e*x],x]},
          -g^(m+1)/e \\[Star] Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Cos[d+e*x]/g]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[(m-1)/2] && IntegerQ[2*p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(d__ + e__ * x_).pow(m_)
            * (a__ + b__ * (f__ * i_cos(d__ + e__ * x_)).pow(n_)
                + c__ * (f__ * i_cos(d__ + e__ * x_)).pow(n2_))
            .pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, f__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let g = rubi_free_factors(&cos, x_);
            let transformed = (Atom::num(1) - g.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__
                    + &b__ * (&f__ * &g * &z).pow(&n_)
                    + &c__ * (&f__ * &g * &z).pow(Atom::num(2) * &n_))
                .pow(&p_)
                / z.pow(&m_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-g.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, cos / &g))
        },
    ));
}

fn push_rules_rule_3761(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3761,
        source: "Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cot = angle.cot();
            let recursive_integrand =
                cot.pow(&m_) * (&b__ + Atom::num(2) * &c__ * sin.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3762,
        source: "Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          1/(4^p*c^p) \\[Star] Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let tan = angle.tan();
            let recursive_integrand =
                tan.pow(&m_) * (&b__ + Atom::num(2) * &c__ * cos.pow(&n_)).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3763,
        source: "Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p) \\[Star] Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let cot = angle.cot();
            let trinomial = &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * sin.pow(&n_);
            let recursive_integrand = cot.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3764,
        source: "Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
          (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p) \\[Star] Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[(m-1)/2]] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [a__, b__, d__, e__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!((&m_ - 1) / 2)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let tan = angle.tan();
            let trinomial = &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let factor = &b__ + Atom::num(2) * &c__ * cos.pow(&n_);
            let recursive_integrand = tan.pow(&m_) * factor.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_) / factor.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3765,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[n2,2*n] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum =
                rubi_expand_to_sum(&(&c__ + &b__ * base.pow(&n_ / 2) + &a__ * base.pow(&n_)), sub);
            let denominator = base.pow(&n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3766,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f^(m+1)/e \\[Star] Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[n2,2*n] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, b__, d__, e__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum =
                rubi_expand_to_sum(&(&c__ + &b__ * base.pow(&n_ / 2) + &a__ * base.pow(&n_)), sub);
            let denominator = base.pow(&n_ * &p_ + 1);
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_) / denominator;
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3767,
        source: "Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/sin[d+e*x]^m,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let sin = (&d__ + &e__ * x_).sin();
            let trinomial =
                &a__ + &b__ * sin.pow(&n_) + &c__ * sin.pow(Atom::num(2) * &n_);
            let payload = (Atom::num(1) - sin.pow(2)).pow(&m_ / 2)
                * trinomial.pow(&p_)
                / sin.pow(&m_);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3768(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 3768,
        source: "Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
          Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/cos[d+e*x]^m,x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && IntegerQ[m/2] && NeQ[b^2-4*a*c,0] && IntegersQ[n,p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, n2_, p_, x_],
        optional: [m_, a__, b__, d__, e__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&m_ / 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([n_, p_])
        },
        rhs: {
            let cos = (&d__ + &e__ * x_).cos();
            let trinomial =
                &a__ + &b__ * cos.pow(&n_) + &c__ * cos.pow(Atom::num(2) * &n_);
            let payload = (Atom::num(1) - cos.pow(2)).pow(&m_ / 2)
                * trinomial.pow(&p_)
                / cos.pow(&m_);
            rubi_rhs_int(&rubi_expand_trig(&payload, x_), x_)
        },
    ));
}

fn push_rules_rule_3769(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3769,
        source: "Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          1/(4^n*c^n) \\[Star] Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c,0] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let recursive_integrand = (&capital_a__ + &capital_b__ * &sin)
                * (&b__ + Atom::num(2) * &c__ * sin).pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&n_) * c__.pow(&n_)), recursive)
        },
    ));
}

fn push_rules_rule_3770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3770,
        source: "Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          1/(4^n*c^n) \\[Star] Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c,0] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let recursive_integrand = (&capital_a__ + &capital_b__ * &cos)
                * (&b__ + Atom::num(2) * &c__ * cos).pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(4).pow(&n_) * c__.pow(&n_)), recursive)
        },
    ));
}

fn push_rules_rule_3771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3771,
        source: "Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          (a+b*Sin[d+e*x]+c*Sin[d+e*x]^2)^n/(b+2*c*Sin[d+e*x])^(2*n) \\[Star] Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let trinomial = &a__ + &b__ * &sin + &c__ * sin.pow(2);
            let factor = &b__ + Atom::num(2) * &c__ * &sin;
            let recursive_integrand =
                (&capital_a__ + &capital_b__ * &sin) * factor.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&n_) / factor.pow(Atom::num(2) * &n_), recursive)
        },
    ));
}

fn push_rules_rule_3772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3772,
        source: "Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          (a+b*Cos[d+e*x]+c*Cos[d+e*x]^2)^n/(b+2*c*Cos[d+e*x])^(2*n) \\[Star] Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let trinomial = &a__ + &b__ * &cos + &c__ * cos.pow(2);
            let factor = &b__ + Atom::num(2) * &c__ * &cos;
            let recursive_integrand =
                (&capital_a__ + &capital_b__ * &cos) * factor.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&n_) / factor.pow(Atom::num(2) * &n_), recursive)
        },
    ));
}

fn push_rules_rule_3773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3773,
        source: "Int[(A_+B_.*sin[d_.+e_.*x_])/(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2),x_Symbol] :=
          Module[{q=Rt[b^2-4*a*c,2]},
          (B+(b*B-2*A*c)/q) \\[Star] Int[1/(b+q+2*c*Sin[d+e*x]),x] +
          (B-(b*B-2*A*c)/q) \\[Star] Int[1/(b-q+2*c*Sin[d+e*x]),x]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(d__ + e__ * x_))
            / (a__ + b__ * i_sin(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_).pow(2)),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, x_],
        optional: [capital_b__, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = angle.sin();
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let coefficient = (&b__ * &capital_b__ - Atom::num(2) * &capital_a__ * &c__) / &q;
            let first_integrand =
                Atom::num(1) / (&b__ + &q + Atom::num(2) * &c__ * &sin);
            let second_integrand =
                Atom::num(1) / (&b__ - &q + Atom::num(2) * &c__ * sin);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__ + &coefficient, first)
                    + rubi_star(&capital_b__ - coefficient, second)
        },
    ));
}

fn push_rules_rule_3774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3774,
        source: "Int[(A_+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2),x_Symbol] :=
          Module[{q=Rt[b^2-4*a*c,2]},
          (B+(b*B-2*A*c)/q) \\[Star] Int[1/(b+q+2*c*Cos[d+e*x]),x] +
          (B-(b*B-2*A*c)/q) \\[Star] Int[1/(b-q+2*c*Cos[d+e*x]),x]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_))
            / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_cos(d__ + e__ * x_).pow(2)),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, x_],
        optional: [capital_b__, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let coefficient = (&b__ * &capital_b__ - Atom::num(2) * &capital_a__ * &c__) / &q;
            let first_integrand =
                Atom::num(1) / (&b__ + &q + Atom::num(2) * &c__ * &cos);
            let second_integrand =
                Atom::num(1) / (&b__ - &q + Atom::num(2) * &c__ * cos);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__ + &coefficient, first)
                    + rubi_star(&capital_b__ - coefficient, second)
        },
    ));
}

fn push_rules_rule_3775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3775,
        source: "Int[(A_+B_.*sin[d_.+e_.*x_])*(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          Int[ExpandTrig[(A+B*sin[d+e*x])*(a+b*sin[d+e*x]+c*sin[d+e*x]^2)^n,x],x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c,0] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let sin = i_sin(&angle);
            let payload = (&capital_a__ + &capital_b__ * &sin)
                * (&a__ + &b__ * &sin + &c__ * sin.pow(2)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3776,
        source: "Int[(A_+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
          Int[ExpandTrig[(A+B*cos[d+e*x])*(a+b*cos[d+e*x]+c*cos[d+e*x]^2)^n,x],x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c,0] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_],
        optional: [capital_b__, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = i_cos(&angle);
            let payload = (&capital_a__ + &capital_b__ * &cos)
                * (&a__ + &b__ * &cos + &c__ * cos.pow(2)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3725_through_3742_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3725..=3742).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3725..=3742).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3743_through_3776_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3743..=3776).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3743..=3776).collect::<Vec<_>>());
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
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_) + c__ * i_cos(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_) + c__ * i_sin(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_))
        * (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_cos(d__ + e__ * x_).pow(2)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_sin(d__ + e__ * x_))
        * (a__ + b__ * i_sin(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_).pow(2)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_) + c__ * i_cos(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_) + c__ * i_sin(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cot(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_) + c__ * i_cos(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cot(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_) + c__ * i_sin(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_) + c__ * i_cos(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_) + c__ * i_sin(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_tan(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_cos(d__ + e__ * x_).pow(n_) + c__ * i_cos(d__ + e__ * x_).pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_tan(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_sin(d__ + e__ * x_).pow(n_) + c__ * i_sin(d__ + e__ * x_).pow(n2_)).pow(p_)
}
