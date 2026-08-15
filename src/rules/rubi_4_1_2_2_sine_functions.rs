use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3312(rules);
    push_rules_rule_3313(rules);
    push_rules_rule_3314(rules);
    push_rules_rule_3315(rules);
    push_rules_rule_3316(rules);
    push_rules_rule_3317(rules);
    push_rules_rule_3318(rules);
    push_rules_rule_3319(rules);
    push_rules_rule_3320(rules);
    push_rules_rule_3321(rules);
    push_rules_rule_3322(rules);
    push_rules_rule_3323(rules);
    push_rules_rule_3324(rules);
    push_rules_rule_3325(rules);
    push_rules_rule_3326(rules);
    push_rules_rule_3327(rules);
    push_rules_rule_3328(rules);
    push_rules_rule_3329(rules);
    push_rules_rule_3330(rules);
    push_rules_rule_3331(rules);
    push_rules_rule_3332(rules);
    push_rules_rule_3333(rules);
    push_rules_rule_3334(rules);
    push_rules_rule_3335(rules);
    push_rules_rule_3336(rules);
    push_rules_rule_3337(rules);
    push_rules_rule_3338(rules);
    push_rules_rule_3339(rules);
    push_rules_rule_3340(rules);
    push_rules_rule_3341(rules);
    push_rules_rule_3342(rules);
    push_rules_rule_3343(rules);
    push_rules_rule_3344(rules);
    push_rules_rule_3345(rules);
    push_rules_rule_3346(rules);
    push_rules_rule_3347(rules);
    push_rules_rule_3348(rules);
    push_rules_rule_3349(rules);
    push_rules_rule_3350(rules);
    push_rules_rule_3351(rules);
    push_rules_rule_3352(rules);
    push_rules_rule_3353(rules);
    push_rules_rule_3354(rules);
    push_rules_rule_3355(rules);
    push_rules_rule_3356(rules);
    push_rules_rule_3357(rules);
    push_rules_rule_3358(rules);
    push_rules_rule_3359(rules);
    push_rules_rule_3360(rules);
    push_rules_rule_3361(rules);
    push_rules_rule_3362(rules);
    push_rules_rule_3363(rules);
    push_rules_rule_3364(rules);
    push_rules_rule_3365(rules);
    push_rules_rule_3366(rules);
    push_rules_rule_3367(rules);
    push_rules_rule_3368(rules);
    push_rules_rule_3369(rules);
    push_rules_rule_3370(rules);
    push_rules_rule_3371(rules);
    push_rules_rule_3372(rules);
    push_rules_rule_3373(rules);
    push_rules_rule_3374(rules);
    push_rules_rule_3375(rules);
    push_rules_rule_3376(rules);
    push_rules_rule_3377(rules);
    push_rules_rule_3378(rules);
    push_rules_rule_3379(rules);
    push_rules_rule_3380(rules);
    push_rules_rule_3381(rules);
    push_rules_rule_3382(rules);
    push_rules_rule_3383(rules);
    push_rules_rule_3384(rules);
    push_rules_rule_3385(rules);
    push_rules_rule_3386(rules);
    push_rules_rule_3387(rules);
    push_rules_rule_3388(rules);
    push_rules_rule_3389(rules);
    push_rules_rule_3390(rules);
    push_rules_rule_3391(rules);
    push_rules_rule_3392(rules);
    push_rules_rule_3393(rules);
    push_rules_rule_3394(rules);
    push_rules_rule_3395(rules);
    push_rules_rule_3396(rules);
    push_rules_rule_3397(rules);
    push_rules_rule_3398(rules);
    push_rules_rule_3399(rules);
    push_rules_rule_3400(rules);
    push_rules_rule_3401(rules);
    push_rules_rule_3402(rules);
    push_rules_rule_3403(rules);
    push_rules_rule_3404(rules);
    push_rules_rule_3405(rules);
    push_rules_rule_3406(rules);
}

fn push_rules_rule_3312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3312,
        source: "Int[cos[e_.+f_.*x_]*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          1/(b*f) \\[Star] Subst[Int[(a+x)^m*(c+d/b*x)^n,x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(e__ + f__ * x_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &z).pow(&m_) * (&c__ + &d__ * &z / &b__).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(Atom::num(1) / (&b__ * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3313,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a \\[Star] Int[Cos[e+f*x]^p*(d*Sin[e+f*x])^n,x] + b/d \\[Star] Int[Cos[e+f*x]^p*(d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[(p-1)/2] && IntegerQ[n] && (LtQ[p,0] && NeQ[a^2-b^2,0] || LtQ[0,n,p-1] || LtQ[p+1,-n,2*p+1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(p_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [e__, f__, d__, n_, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_, p_], x_)
                && integerq!((&p_ - 1) / 2)
                && integerq!(n_)
                && (ltq!(p_, 0) && neq!(a__.pow(2) - b__.pow(2), 0)
                    || ltq!(0, n_, &p_ - 1)
                    || ltq!(&p_ + 1, Atom::num(0) - &n_)
                        && ltq!(Atom::num(0) - &n_, Atom::num(2) * &p_ + 1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 =
                rubi_rhs_int(&(angle.cos().pow(&p_) * (&d__ * angle.sin()).pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(angle.cos().pow(&p_) * (&d__ * angle.sin()).pow(&n_ + 1)), x_);

            rubi_star(a__, recursive1)
                    + rubi_star(&b__ / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3314,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[Cos[e+f*x]^(p-2)*(d*Sin[e+f*x])^n,x] -
          1/(b*d) \\[Star] Int[Cos[e+f*x]^(p-2)*(d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2,0] && IntegerQ[n] && (LtQ[0,n,(p+1)/2] || LeQ[p,-n] && LtQ[-n,2*p-3] || GtQ[n,0] && LeQ[n,-p])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(p_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [e__, f__, d__, n_, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_, p_], x_)
                && integerq!((&p_ - 1) / 2)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(n_)
                && (ltq!(0, n_, (&p_ + 1) / 2)
                    || leq!(p_, Atom::num(0) - &n_)
                        && ltq!(Atom::num(0) - &n_, Atom::num(2) * &p_ - 3)
                    || gtq!(n_, 0) && leq!(n_, Atom::num(0) - &p_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(angle.cos().pow(&p_ - 2) * (&d__ * angle.sin()).pow(&n_)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(angle.cos().pow(&p_ - 2) * (&d__ * angle.sin()).pow(&n_ + 1)),
                x_,
            );

            rubi_star(Atom::num(1) / &a__, recursive1)
                    - rubi_star(Atom::num(1) / (&b__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3315,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          1/(b^p*f) \\[Star] Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2)*(c+d/b*x)^n,x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && integerq!((&p_ - 1) / 2)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &z).pow(&m_ + (&p_ - 1) / 2)
                * (&a__ - &z).pow((&p_ - 1) / 2)
                * (&c__ + &d__ * &z / &b__).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(Atom::num(1) / (b__.pow(&p_) * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3316,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          1/(b^p*f) \\[Star] Subst[Int[(a+x)^m*(c+d/b*x)^n*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IntegerQ[(p-1)/2] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && integerq!((&p_ - 1) / 2)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &z).pow(&m_)
                * (&c__ + &d__ * &z / &b__).pow(&n_)
                * (b__.pow(2) - z.pow(2)).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(Atom::num(1) / (b__.pow(&p_) * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3317,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n,x] + b/d \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, n_, b__],
        when: { freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * (&d__ * angle.sin()).pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * (&d__ * angle.sin()).pow(&n_ + 1)), x_);

            rubi_star(a__, recursive1)
                    + rubi_star(&b__ / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3318,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g^2/a \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] -
          g^2/(b*d) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, n_, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_ - 2) * (&d__ * angle.sin()).pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(scaled_cos.pow(&p_ - 2) * (&d__ * angle.sin()).pow(&n_ + 1)), x_);

            rubi_star(g__.pow(2) / &a__, recursive1)
                    - rubi_star(g__.pow(2) / (&b__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3319,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^m*c^m/g^(2*m) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && Not[IntegerQ[n] && LtQ[n^2,m^2]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && !(integerq!(n_) && ltq!(n_.pow(2), m_.pow(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(Atom::num(2) * &m_ + &p_)
                * (&c__ + &d__ * angle.sin()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&m_) * c__.pow(&m_)
                    / g__.pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3320,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          1/(a^(p/2)*c^(p/2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+p/2)*(c+d*Sin[e+f*x])^(n+p/2),x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&p_ / 2)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + &p_ / 2)
                * (&c__ + &d__ * angle.sin()).pow(&n_ + &p_ / 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / (a__.pow(&p_ / 2) * c__.pow(&p_ / 2)), recursive)
        },
    ));
}

fn push_rules_rule_3321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3321,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          g*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) \\[Star] Int[(g*Cos[e+f*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
                * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [g__, e__, f__, p_, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive = rubi_rhs_int(&scaled_cos.pow(&p_ - 1), x_);

            rubi_star(&g__ * angle.cos()
                    / ((&a__ + &b__ * angle.sin()).sqrt()
                        * (&c__ + &d__ * angle.sin()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3322,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
            (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m])) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[2*m+p-1,0] && EqQ[m-n-1,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(Atom::num(2) * &m_ + &p_ - 1, 0)
                && eqq!(&m_ - &n_ - 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let recursive_integrand = scaled_cos.pow(Atom::num(2) * &m_ + &p_)
                / (&c__ + &d__ * i_sin(&angle));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&int_m)
                    * c__.pow(&int_m)
                    * (&a__ + &b__ * i_sin(&angle)).pow(&frac_m)
                    * (&c__ + &d__ * i_sin(&angle)).pow(&frac_m)
                    / (g__.pow(Atom::num(2) * &int_m)
                        * scaled_cos.pow(Atom::num(2) * frac_m)), recursive)
        },
    ));
}

fn push_rules_rule_3323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3323,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m-n-1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[2*m+p-1,0] && NeQ[m-n-1,0]",
        desc: "Doubly degenerate sine recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(Atom::num(2) * &m_ + &p_ - 1, 0)
                && neq!(&m_ - &n_ - 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&f__ * &g__ * (&m_ - &n_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_3324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3324,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(2*n+p+1)) -
          b*(2*m+p-1)/(d*(2*n+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IGtQ[Simplify[m+p/2-1/2],0] && LtQ[n,-1] &&
          NeQ[2*n+p+1,0] && Not[ILtQ[Simplify[m+n+p],0] && GtQ[Simplify[2*m+n+3*p/2+1],0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            let s1 = rubi_simplify(&(&m_ + &p_ / 2 - Atom::num(1) / Atom::num(2)));
            let s2 = rubi_simplify(&(&m_ + &n_ + &p_));
            let s3 = rubi_simplify(&(Atom::num(2) * &m_ + &n_ + Atom::num(3) * &p_ / 2 + 1));
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(s1, 0)
                && ltq!(n_, -1)
                && neq!(Atom::num(2) * &n_ + &p_ + 1, 0)
                && !(iltq!(s2, 0) && gtq!(s3, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&f__ * &g__ * (Atom::num(2) * &n_ + &p_ + 1))), x_)
                    - rubi_star(&b__ * (Atom::num(2) * &m_ + &p_ - 1)
                            / (&d__ * (Atom::num(2) * &n_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3325,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m+n+p)) +
          a*(2*m+p-1)/(m+n+p) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IGtQ[Simplify[m+p/2-1/2],0] && Not[LtQ[n,-1]] &&
          Not[IGtQ[Simplify[n+p/2-1/2],0] && GtQ[m-n,0]] && Not[ILtQ[Simplify[m+n+p],0] && GtQ[Simplify[2*m+n+3*p/2+1],0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            let s1 = rubi_simplify(&(&m_ + &p_ / 2 - Atom::num(1) / Atom::num(2)));
            let s2 = rubi_simplify(&(&n_ + &p_ / 2 - Atom::num(1) / Atom::num(2)));
            let s3 = rubi_simplify(&(&m_ + &n_ + &p_));
            let s4 = rubi_simplify(&(Atom::num(2) * &m_ + &n_ + Atom::num(3) * &p_ / 2 + 1));
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(s1, 0)
                && !ltq!(n_, -1)
                && !(igtq!(s2, 0) && gtq!(&m_ - &n_, 0))
                && !(iltq!(s3, 0) && gtq!(s4, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&f__ * &g__ * (&m_ + &n_ + &p_))), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &m_ + &p_ - 1)
                            / (&m_ + &n_ + &p_), recursive)
        },
    ));
}

fn push_rules_rule_3326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3326,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
            (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m])) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[2*m+p+1,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(m_),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(Atom::num(2) * &m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let recursive = rubi_rhs_int(&scaled_cos.pow(Atom::num(2) * &m_ + &p_), x_);

            rubi_star(a__.pow(&int_m)
                    * c__.pow(&int_m)
                    * (&a__ + &b__ * angle.sin()).pow(&frac_m)
                    * (&c__ + &d__ * angle.sin()).pow(&frac_m)
                    / (g__.pow(Atom::num(2) * &int_m)
                        * scaled_cos.pow(Atom::num(2) * frac_m)), recursive)
        },
    ));
}

fn push_rules_rule_3327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3327,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(m-n)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[m+n+p+1,0] && NeQ[m,n]",
        desc: "Doubly degenerate sine recurrence 1c with n\\[Rule]-m-p-1",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ + &n_ + &p_ + 1, 0)
                && neq!(m_, n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&a__ * &f__ * &g__ * (&m_ - &n_))), x_)
        },
    ));
}

fn push_rules_rule_3328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3328,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(2*m+p+1)) +
          (m+n+p+1)/(a*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && ILtQ[Simplify[m+n+p+1],0] && NeQ[2*m+p+1,0] &&
          (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            let s = rubi_simplify(&(&m_ + &n_ + &p_ + 1));
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(s, 0)
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                && (sum_simplerq!(m_, 1) || !sum_simplerq!(n_, 1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ + 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&a__ * &f__ * &g__ * (Atom::num(2) * &m_ + &p_ + 1))), x_)
                    + rubi_star((&m_ + &n_ + &p_ + 1)
                            / (&a__ * (Atom::num(2) * &m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3329,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(2*n+p+1)) -
          b*(2*m+p-1)/(d*(2*n+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && GtQ[m,0] && LtQ[n,-1] && NeQ[2*n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Doubly degenerate sine recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && ltq!(n_, -1)
                && neq!(Atom::num(2) * &n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&f__ * &g__ * (Atom::num(2) * &n_ + &p_ + 1))), x_)
                    - rubi_star(&b__ * (Atom::num(2) * &m_ + &p_ - 1)
                            / (&d__ * (Atom::num(2) * &n_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3330,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m+n+p)) +
          a*(2*m+p-1)/(m+n+p) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && GtQ[m,0] && NeQ[m+n+p,0] && Not[LtQ[0,n,m]] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && neq!(&m_ + &n_ + &p_, 0)
                && !ltq!(0, n_, m_)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_ - 1) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&f__ * &g__ * (&m_ + &n_ + &p_))), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &m_ + &p_ - 1)
                            / (&m_ + &n_ + &p_), recursive)
        },
    ));
}

fn push_rules_rule_3331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3331,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(2*m+p+1)) +
          (m+n+p+1)/(a*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && LtQ[m,-1] && NeQ[2*m+p+1,0] && Not[LtQ[m,n,-1]] &&
          IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                && !ltq!(m_, n_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_ + 1)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                    / (&a__ * &f__ * &g__ * (Atom::num(2) * &m_ + &p_ + 1))), x_)
                    + rubi_star((&m_ + &n_ + &p_ + 1)
                            / (&a__ * (Atom::num(2) * &m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3332,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
            (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m])) \\[Star]
            Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && (FractionQ[m] || Not[FractionQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (fractionq!(m_) || !fractionq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let recursive_integrand = scaled_cos.pow(Atom::num(2) * &m_ + &p_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&int_m)
                    * c__.pow(&int_m)
                    * (&a__ + &b__ * i_sin(&angle)).pow(&frac_m)
                    * (&c__ + &d__ * i_sin(&angle)).pow(&frac_m)
                    / (g__.pow(Atom::num(2) * &int_m)
                        * scaled_cos.pow(Atom::num(2) * frac_m)), recursive)
        },
    ));
}

fn push_rules_rule_3333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3333,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && EqQ[a*d*m+b*c*(m+p+1),0]",
        desc: "Singly degenerate sine recurrence 2c with c\\[Rule]1,d\\[Rule]0,n\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + &p_ + 1), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();

            rubi_simp(&(-&d__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&f__ * &g__ * (&m_ + &p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3334,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(b*c+a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) +
          b*(a*d*m+b*c*(m+p+1))/(a*g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[a^2-b^2,0] && GtQ[m,-1] && LtQ[p,-1]",
        desc: "Singly degenerate sine recurrence 4a with c\\[Rule]1,d\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, -1)
                && ltq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ + 2) * (&a__ + &b__ * angle.sin()).pow(&m_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-(&b__ * &c__ + &a__ * &d__) * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(&b__
                            * (&a__ * &d__ * &m_
                                + &b__ * &c__ * (&m_ + &p_ + 1))
                            / (&a__ * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3335,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) +
          (a*d*m+b*c*(m+p+1))/(b*(m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && IGtQ[Simplify[(2*m+p+1)/2],0] && NeQ[m+p+1,0]",
        desc: "Singly degenerate sine recurrence 2c with c\\[Rule]1,d\\[Rule]0,n\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            let s = rubi_simplify(&((Atom::num(2) * &m_ + &p_ + 1) / 2));
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(s, 0)
                && neq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&f__ * &g__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star((&a__ * &d__ * &m_
                            + &b__ * &c__ * (&m_ + &p_ + 1))
                            / (&b__ * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3336,
        source: "Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          2*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(2*m+3)) +
          1/(b^3*(2*m+3)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+2)*(b*c+2*a*d*(m+1)-b*d*(2*m+3)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[a^2-b^2,0] && LtQ[m,-3/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, a__, b__, m_, c__, d__, x_],
        optional: [e__, f__, b__, c__, d__],
        when: {
            let minus_three_halves = Atom::num(-3) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, minus_three_halves)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 2)
                * (&b__ * &c__ + Atom::num(2) * &a__ * &d__ * (&m_ + 1)
                    - &b__ * &d__ * (Atom::num(2) * &m_ + 3) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(2) * (&b__ * &c__ - &a__ * &d__) * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (b__.pow(2) * &f__ * (Atom::num(2) * &m_ + 3))), x_)
                    + rubi_star(Atom::num(1)
                            / (b__.pow(3) * (Atom::num(2) * &m_ + 3)), recursive)
        },
    ));
}

fn push_rules_rule_3337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3337,
        source: "Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          d*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)/(b^2*f*(m+3)) -
          1/(b^2*(m+3)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(b*d*(m+2)-a*c*(m+3)+(b*c*(m+3)-a*d*(m+4))*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[a^2-b^2,0] && GeQ[m,-3/2] && LtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, a__, b__, m_, c__, d__, x_],
        optional: [e__, f__, b__, c__, d__],
        when: {
            let minus_three_halves = Atom::num(-3) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && geq!(m_, minus_three_halves)
                && ltq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&b__ * &d__ * (&m_ + 2) - &a__ * &c__ * (&m_ + 3)
                    + (&b__ * &c__ * (&m_ + 3) - &a__ * &d__ * (&m_ + 4)) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&d__ * angle.cos() * (&a__ + &b__ * angle.sin()).pow(&m_ + 2)
                    / (b__.pow(2) * &f__ * (&m_ + 3))), x_)
                    - rubi_star(Atom::num(1) / (b__.pow(2) * (&m_ + 3)), recursive)
        },
    ));
}

fn push_rules_rule_3338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3338,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (b*c-a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) +
          (a*d*m+b*c*(m+p+1))/(a*b*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && (LtQ[m,-1] || ILtQ[Simplify[m+p],0]) && NeQ[2*m+p+1,0]",
        desc: "Singly degenerate sine recurrence 2b with c\\[Rule]1,d\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, c__, d__],
        when: {
            let s = rubi_simplify(&(&m_ + &p_));
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (ltq!(m_, -1) || iltq!(s, 0))
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&b__ * &c__ - &a__ * &d__) * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * &g__ * (Atom::num(2) * &m_ + &p_ + 1))), x_)
                    + rubi_star((&a__ * &d__ * &m_
                            + &b__ * &c__ * (&m_ + &p_ + 1))
                            / (&a__
                                * &b__
                                * (Atom::num(2) * &m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3339,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) +
          (a*d*m+b*c*(m+p+1))/(b*(m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && NeQ[m+p+1,0]",
        desc: "Singly degenerate sine recurrence 2c with c\\[Rule]1,d\\[Rule]0,n\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&f__ * &g__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star((&a__ * &d__ * &m_
                            + &b__ * &c__ * (&m_ + &p_ + 1))
                            / (&b__ * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, w_);
    rules.push(rubi_rule!(
        order: 3340,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])/(f*g*(p+1)) +
          1/(g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*Simp[a*c*(p+2)+b*d*m+b*c*(m+p+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2,0] && GtQ[m,0] && LtQ[p,-1] && IntegerQ[2*m] &&
          Not[EqQ[m,1] && NeQ[c^2-d^2,0] && SimplerQ[c+d*x,a+b*x]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, w_, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            w_ == x_
                && freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &m_)
                && !(eqq!(m_, 1)
                    && neq!(c__.pow(2) - d__.pow(2), 0)
                    && simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let simp = rubi_simp(
                &(&a__ * &c__ * (&p_ + 2)
                    + &b__ * &d__ * &m_
                    + &b__ * &c__ * (&m_ + &p_ + 2) * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_ + 2) * (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled_cos.pow(&p_ + 1)
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin())
                    / (&f__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, w_);
    rules.push(rubi_rule!(
        order: 3341,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) +
          1/(m+p+1) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*Simp[a*c*(m+p+1)+b*d*m+(a*d*m+b*c*(m+p+1))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2,0] && GtQ[m,0] && Not[LtQ[p,-1]] && IntegerQ[2*m] &&
          Not[EqQ[m,1] && NeQ[c^2-d^2,0] && SimplerQ[c+d*x,a+b*x]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, w_, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            w_ == x_
                && freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && !ltq!(p_, -1)
                && integerq!(Atom::num(2) * &m_)
                && !(eqq!(m_, 1)
                    && neq!(c__.pow(2) - d__.pow(2), 0)
                    && simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let simp = rubi_simp(
                &(&a__ * &c__ * (&m_ + &p_ + 1)
                    + &b__ * &d__ * &m_
                    + (&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + &p_ + 1)) * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_ - 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&d__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&f__ * &g__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&m_ + &p_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3342,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(b*c*(m+p+1)-a*d*p+b*d*(m+1)*Sin[e+f*x])/(b^2*f*(m+1)*(m+p+1)) +
          g^2*(p-1)/(b^2*(m+1)*(m+p+1)) \\[Star]
            Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Simp[b*d*(m+1)+(b*c*(m+p+1)-a*d*p)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && GtQ[p,1] && NeQ[m+p+1,0] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 2a with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]A,C\\[Rule]B,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && gtq!(p_, 1)
                && neq!(&m_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let simp = rubi_simp(
                &(&b__ * &d__ * (&m_ + 1)
                    + (&b__ * &c__ * (&m_ + &p_ + 1) - &a__ * &d__ * &p_) * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_ - 2) * (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1)
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    * (&b__ * &c__ * (&m_ + &p_ + 1) - &a__ * &d__ * &p_
                        + &b__ * &d__ * (&m_ + 1) * angle.sin())
                    / (b__.pow(2) * &f__ * (&m_ + 1) * (&m_ + &p_ + 1))), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1)
                            / (b__.pow(2)
                                * (&m_ + 1)
                                * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3343,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -(b*c-a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) +
          1/((a^2-b^2)*(m+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(b*c-a*d)*(m+p+2)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 1c with c\\[Rule]1,d\\[Rule]0,C\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let discriminant = a__.pow(2) - b__.pow(2);
            let simp = rubi_simp(
                &((&a__ * &c__ - &b__ * &d__) * (&m_ + 1)
                    - (&b__ * &c__ - &a__ * &d__) * (&m_ + &p_ + 2) * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_ + 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-(&b__ * &c__ - &a__ * &d__)
                    * scaled_cos.pow(&p_ + 1)
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&f__ * &g__ * &discriminant * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (discriminant * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3344,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(b*c*(m+p+1)-a*d*p+b*d*(m+p)*Sin[e+f*x])/(b^2*f*(m+p)*(m+p+1)) +
          g^2*(p-1)/(b^2*(m+p)*(m+p+1)) \\[Star]
            Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*Simp[b*(a*d*m+b*c*(m+p+1))+(a*b*c*(m+p+1)-d*(a^2*p-b^2*(m+p)))*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[a^2-b^2,0] && GtQ[p,1] && NeQ[m+p,0] && NeQ[m+p+1,0] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 2b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]A,C\\[Rule]B,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(p_, 1)
                && neq!(&m_ + &p_, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let simp = rubi_simp(
                &(&b__ * (&a__ * &d__ * &m_ + &b__ * &c__ * (&m_ + &p_ + 1))
                    + (&a__ * &b__ * &c__ * (&m_ + &p_ + 1)
                        - &d__ * (a__.pow(2) * &p_ - b__.pow(2) * (&m_ + &p_)))
                        * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_ - 2) * (&a__ + &b__ * angle.sin()).pow(&m_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1)
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    * (&b__ * &c__ * (&m_ + &p_ + 1) - &a__ * &d__ * &p_
                        + &b__ * &d__ * (&m_ + &p_) * angle.sin())
                    / (b__.pow(2) * &f__ * (&m_ + &p_) * (&m_ + &p_ + 1))), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1)
                            / (b__.pow(2)
                                * (&m_ + &p_)
                                * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3345,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(b*c-a*d-(a*c-b*d)*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) +
          1/(g^2*(a^2-b^2)*(p+1)) \\[Star]
            Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*Simp[c*(a^2*(p+2)-b^2*(m+p+2))+a*b*d*m+b*(a*c-b*d)*(m+p+3)*Sin[e+f*x],x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[a^2-b^2,0] && LtQ[p,-1] && IntegerQ[2*m]",
        desc: "Nondegenerate sine recurrence 3b with c\\[Rule]1,d\\[Rule]0,C\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let discriminant = a__.pow(2) - b__.pow(2);
            let simp = rubi_simp(
                &(&c__ * (a__.pow(2) * (&p_ + 2) - b__.pow(2) * (&m_ + &p_ + 2))
                    + &a__ * &b__ * &d__ * &m_
                    + &b__ * (&a__ * &c__ - &b__ * &d__) * (&m_ + &p_ + 3) * angle.sin()),
                x_,
            );
            let recursive_integrand =
                scaled_cos.pow(&p_ + 2) * (&a__ + &b__ * angle.sin()).pow(&m_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(scaled_cos.pow(&p_ + 1)
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    * (&b__ * &c__ - &a__ * &d__ - (&a__ * &c__ - &b__ * &d__) * angle.sin())
                    / (&f__ * &g__ * &discriminant * (&p_ + 1))), x_)
                    + rubi_star(Atom::num(1)
                            / (g__.pow(2) * discriminant * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3346,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(c_.+d_.*sin[e_.+f_.*x_])/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          d/b \\[Star] Int[(g*Cos[e+f*x])^p,x] + (b*c-a*d)/b \\[Star] Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (c__ + d__ * i_sin(e__ + f__ * x_))
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, p_, c__, d__, a__, b__, x_],
        optional: [g__, e__, f__, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive1 = rubi_rhs_int(&scaled_cos.pow(&p_), x_);
            let recursive2 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) / (&a__ + &b__ * angle.sin())), x_);

            rubi_star(&d__ / &b__, recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3347,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          c*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2)) \\[Star]
            Subst[Int[(1+d/c*x)^((p+1)/2)*(1-d/c*x)^((p-1)/2)*(a+b*x)^m,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && NeQ[a^2-b^2,0] && EqQ[c^2-d^2,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (Atom::num(1) + &d__ * &z / &c__).pow((&p_ + 1) / 2)
                * (Atom::num(1) - &d__ * &z / &c__).pow((&p_ - 1) / 2)
                * (&a__ + &b__ * &z).pow(&m_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();

            let substituted = rubi_subst(&primitive, sub, angle.sin());

            rubi_star(&c__ * &g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (Atom::num(1) + angle.sin()).pow((&p_ - 1) / 2)
                        * (Atom::num(1) - angle.sin()).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3348,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^(2*m) \\[Star] Int[(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2,0] && IntegersQ[m,p] && EqQ[2*m+p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, p_, a__, b__, m_, d__, n_, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, p_])
                && eqq!(Atom::num(2) * &m_ + &p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&d__ * angle.sin()).pow(&n_) / (&a__ - &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3349,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(2*b*f*g*(m+1)) +
          a/(2*g^2) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && EqQ[m-p,0]",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]a2,B\\[Rule]2 a b,C\\[Rule]b2,m\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ - &p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ + 2) * (&a__ + &b__ * angle.sin()).pow(&m_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (Atom::num(2) * &b__ * &f__ * &g__ * (&m_ + 1))), x_)
                    + rubi_star(&a__ / (Atom::num(2) * g__.pow(2)), recursive)
        },
    ));
}

fn push_rules_rule_3350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3350,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*m) -
          1/g^2 \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && EqQ[m+p+1,0]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ + 2) * (&a__ + &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * &g__ * &m_)), x_)
                    - rubi_star(Atom::num(1) / g__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3351,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          1/a^p \\[Star] Int[ExpandTrig[(d*sin[e+f*x])^n*(a-b*sin[e+f*x])^(p/2)*(a+b*sin[e+f*x])^(m+p/2),x],x] /;
        FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2,0] && IntegersQ[m,n,p/2] && (GtQ[m,0] && GtQ[p,0] && LtQ[-m-p,n,-1] || GtQ[m,2] && LtQ[p,0] && GtQ[m+p/2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            let lower = -&m_ - &p_;
            freeq!([a__, b__, d__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, n_, &p_ / 2])
                && (gtq!(m_, 0) && gtq!(p_, 0) && ltq!(lower, n_, -1)
                    || gtq!(m_, 2) && ltq!(p_, 0) && gtq!(&m_ + &p_ / 2, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let expanded = rubi_expand_trig(
                &((&d__ * i_sin(&angle)).pow(&n_)
                    * (&a__ - &b__ * i_sin(&angle)).pow(&p_ / 2)
                    * (&a__ + &b__ * i_sin(&angle)).pow(&m_ + &p_ / 2)),
                x_,
            );
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / a__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3352,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let u = (&g__ * i_cos(&angle)).pow(&p_);
            let v = (&d__ * i_sin(&angle)).pow(&n_) * (&a__ + &b__ * i_sin(&angle)).pow(&m_);
            let expanded = rubi_expand_trig_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3353,
        source: "Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          1/b^2 \\[Star] Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1)*(a-b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && (ILtQ[m,0] || Not[IGtQ[n,0]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (iltq!(m_, 0) || !igtq!(n_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&d__ * angle.sin()).pow(&n_)
                * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&a__ - &b__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3354,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (a/g)^(2*m) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)*(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2,0] && ILtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand =
                scaled_cos.pow(Atom::num(2) * &m_ + &p_) * (&d__ * i_sin(&angle)).pow(&n_)
                    / (&a__ - &b__ * i_sin(&angle)).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ / &g__).pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3355,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (a/g)^(2*m) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)*(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,d,e,f,g,n},x] && EqQ[a^2-b^2,0] && IntegerQ[m] && RationalQ[p] && (EqQ[2*m+p,0] || GtQ[2*m+p,0] && LtQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && rationalq!(p_)
                && (eqq!(Atom::num(2) * &m_ + &p_, 0)
                    || gtq!(Atom::num(2) * &m_ + &p_, 0) && ltq!(p_, -1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand =
                scaled_cos.pow(Atom::num(2) * &m_ + &p_) * (&d__ * i_sin(&angle)).pow(&n_)
                    / (&a__ - &b__ * i_sin(&angle)).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ / &g__).pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3356,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) -
          1/(a^2*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m+p+1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && LeQ[m,-1/2] && NeQ[2*m+p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, b__],
        when: {
            let minus_half = -Atom::num(1) / Atom::num(2);
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && leq!(m_, minus_half)
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&a__ * &m_ - &b__ * (Atom::num(2) * &m_ + &p_ + 1) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&a__ * &f__ * &g__ * (Atom::num(2) * &m_ + &p_ + 1))), x_)
                    - rubi_star(Atom::num(1)
                            / (a__.pow(2) * (Atom::num(2) * &m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3357,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*g*(m+p+2)) +
          1/(b*(m+p+2)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m*(b*(m+1)-a*(p+1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && NeQ[m+p+2,0]",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]a2,B\\[Rule]2 a b,C\\[Rule]b2,m\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(&m_ + &p_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&b__ * (&m_ + 1) - &a__ * (&p_ + 1) * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled_cos.pow(&p_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&b__ * &f__ * &g__ * (&m_ + &p_ + 2))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * (&m_ + &p_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3358,
        source: "Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          1/b^2 \\[Star] Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1)*(a-b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && IntegersQ[2*m,2*n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&d__ * angle.sin()).pow(&n_)
                * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&a__ - &b__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3359,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -2/(a*b*d) \\[Star] Int[(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+2),x] +
          1/a^2 \\[Star] Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+2)*(1+Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2,0] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&d__ * angle.sin()).pow(&n_ + 1) * (&a__ + &b__ * angle.sin()).pow(&m_ + 2)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&d__ * angle.sin()).pow(&n_)
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 2)
                    * (Atom::num(1) + angle.sin().pow(2))),
                x_,
            );

            rubi_star(-Atom::num(2) / (&a__ * &b__ * &d__), recursive1) + rubi_star(Atom::num(1) / a__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3360,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          1/d^4 \\[Star] Int[(d*Sin[e+f*x])^(n+4)*(a+b*Sin[e+f*x])^m,x] +
          Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && Not[IGtQ[m,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&d__ * angle.sin()).pow(&n_ + 4) * (&a__ + &b__ * angle.sin()).pow(&m_)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&d__ * angle.sin()).pow(&n_)
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (Atom::num(1) - Atom::num(2) * angle.sin().pow(2))),
                x_,
            );

            rubi_star(Atom::num(1) / d__.pow(4), recursive1) + recursive2
        },
    ));
}

fn push_rules_rule_3361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3361,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]]) \\[Star]
            Subst[Int[(d*x)^n*(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2,0] && IntegerQ[p/2] && IntegerQ[m]",
        desc: "Algebraic expansion, piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&p_ / 2)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&d__ * &z).pow(&n_)
                * (Atom::num(1) + &b__ * &z / &a__).pow(&m_ + (&p_ - 1) / 2)
                * (Atom::num(1) - &b__ * &z / &a__).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));

            rubi_star(a__.pow(&m_) * angle.cos()
                    / (&f__
                        * (Atom::num(1) + i_sin(&angle)).sqrt()
                        * (Atom::num(1) - i_sin(&angle)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3362,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Cos[e+f*x]/(a^(p-2)*f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]) \\[Star]
            Subst[Int[(d*x)^n(a+b*x)^(m+p/2-1/2)*(a-b*x)^(p/2-1/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && IntegerQ[p/2] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&p_ / 2)
                && !integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&d__ * &z).pow(&n_)
                * (&a__ + &b__ * &z).pow(&m_ + &p_ / 2 - Atom::num(1) / Atom::num(2))
                * (&a__ - &b__ * &z).pow(&p_ / 2 - Atom::num(1) / Atom::num(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));

            rubi_star(angle.cos()
                    / (a__.pow(&p_ - 2)
                        * &f__
                        * (&a__ + &b__ * i_sin(&angle)).sqrt()
                        * (&a__ - &b__ * i_sin(&angle)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3363,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2,0] && IGtQ[m,0] && (IntegerQ[p] || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
                && (integerq!(p_) || igtq!(n_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let u = (&g__ * i_cos(&angle)).pow(&p_);
            let v = (&d__ * i_sin(&angle)).pow(&n_) * (&a__ + &b__ * i_sin(&angle)).pow(&m_);
            let expanded = rubi_expand_trig_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3364,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a^m*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2)) \\[Star]
            Subst[Int[(d*x)^n*(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,d,e,f,n,p},x] && EqQ[a^2-b^2,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&d__ * &z).pow(&n_)
                * (Atom::num(1) + &b__ * &z / &a__).pow(&m_ + (&p_ - 1) / 2)
                * (Atom::num(1) - &b__ * &z / &a__).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));

            rubi_star(a__.pow(&m_) * &g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (Atom::num(1) + i_sin(&angle)).pow((&p_ - 1) / 2)
                        * (Atom::num(1) - i_sin(&angle)).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3365,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)/(f*(a+b*Sin[e+f*x])^((p-1)/2)*(a-b*Sin[e+f*x])^((p-1)/2)) \\[Star]
            Subst[Int[(d*x)^n*(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,d,e,f,m,n,p},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&d__ * &z).pow(&n_)
                * (&a__ + &b__ * &z).pow(&m_ + (&p_ - 1) / 2)
                * (&a__ - &b__ * &z).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));

            rubi_star(&g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (&a__ + &b__ * i_sin(&angle)).pow((&p_ - 1) / 2)
                        * (&a__ - &b__ * i_sin(&angle)).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3366,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -g*(g*Cos[e+f*x])^(p-1)*Sqrt[d*Sin[e+f*x]]*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(m+1)) +
          g^2*(2*m+3)/(2*a*(m+1)) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)/Sqrt[d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && EqQ[m+p+1/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && eqq!(&m_ + &p_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ - 2)
                * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                / (&d__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&g__ * scaled_cos.pow(&p_ - 1) * (&d__ * angle.sin()).sqrt()
                    * (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                    / (&a__ * &d__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(g__.pow(2) * (Atom::num(2) * &m_ + 3)
                            / (Atom::num(2) * &a__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3367,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
          2*(g*Cos[e+f*x])^(p+1)*Sqrt[d*Sin[e+f*x]]*(a+b*Sin[e+f*x])^m/(d*f*g*(2*m+1)) +
          2*a*m/(g^2*(2*m+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)/Sqrt[d*Sin[e+f*x]],x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && GtQ[m,0] && EqQ[m+p+3/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && eqq!(&m_ + &p_ + Atom::num(3) / Atom::num(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ + 2)
                * (&a__ + &b__ * angle.sin()).pow(&m_ - 1)
                / (&d__ * angle.sin()).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(2) * scaled_cos.pow(&p_ + 1) * (&d__ * angle.sin()).sqrt()
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    / (&d__ * &f__ * &g__ * (Atom::num(2) * &m_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &a__ * &m_
                            / (g__.pow(2) * (Atom::num(2) * &m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3368,
        source: "Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*(1-Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&d__ * angle.sin()).pow(&n_)
                * (&a__ + &b__ * angle.sin()).pow(&m_)
                * (Atom::num(1) - angle.sin().pow(2));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3369,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(n+1)) -
          (a^2*(n+1)-b^2*(m+n+2))*Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(a^2*b*d^2*f*(n+1)*(m+1)) +
          1/(a^2*b*d*(n+1)*(m+1)) \\[Star] Int[(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)*
            Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0] && IntegersQ[2*m,2*n] && LtQ[m,-1] && LtQ[n,-1]",
        desc: "Algebraic expansion and sine recurrence 3b with A\\[Rule]1,B\\[Rule]0,C\\[Rule]-2,m\\[Rule]n,n\\[Rule]p, 2b with A\\[Rule]-b (m+n+2),B\\[Rule]-a n,C\\[Rule]b (n+p+3),m\\[Rule]n+1,n\\[Rule]p and\\n\\t\\t\\t2a with A\\[Rule]0,B\\[Rule]0,C\\[Rule]1,m\\[Rule]n+4-2,n\\[Rule]p",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && ltq!(m_, -1)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * (&n_ + 1) * (&n_ + 2)
                    - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 3)
                    + &a__ * &b__ * (&m_ + 1) * &sin
                    - (&a__.pow(2) * (&n_ + 1) * (&n_ + 3)
                        - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 4))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&d__ * &sin).pow(&n_ + 1) * (&a__ + &b__ * &sin).pow(&m_ + 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&cos * (&d__ * &sin).pow(&n_ + 1) * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&a__ * &d__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&((&a__.pow(2) * (&n_ + 1) - &b__.pow(2) * (&m_ + &n_ + 2))
                        * &cos
                        * (&d__ * &sin).pow(&n_ + 2)
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        / (a__.pow(2)
                            * &b__
                            * d__.pow(2)
                            * &f__
                            * (&n_ + 1)
                            * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(1)
                            / (a__.pow(2)
                                * &b__
                                * &d__
                                * (&n_ + 1)
                                * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3370,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) +
          (a^2*(n-m+1)-b^2*(m+n+2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(a^2*b^2*d*f*(m+1)*(m+2)) -
          1/(a^2*b^2*(m+1)*(m+2)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^n*
            Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+3)+a*b*(m+2)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2,0] && IntegersQ[2*m,2*n] && LtQ[m,-1] && Not[LtQ[n,-1]] && (LtQ[m,-2] || EqQ[m+n+4,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && ltq!(m_, -1)
                && !ltq!(n_, -1)
                && (ltq!(m_, -2) || eqq!(&m_ + &n_ + 4, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * (&n_ + 1) * (&n_ + 3)
                    - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 3)
                    + &a__ * &b__ * (&m_ + 2) * &sin
                    - (&a__.pow(2) * (&n_ + 2) * (&n_ + 3)
                        - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 4))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&a__ + &b__ * &sin).pow(&m_ + 2) * (&d__ * &sin).pow(&n_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((a__.pow(2) - b__.pow(2))
                    * &cos
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&d__ * &sin).pow(&n_ + 1)
                    / (&a__ * b__.pow(2) * &d__ * &f__ * (&m_ + 1))), x_)
                    + rubi_simp(&((&a__.pow(2) * (&n_ - &m_ + 1) - &b__.pow(2) * (&m_ + &n_ + 2))
                        * &cos
                        * (&a__ + &b__ * &sin).pow(&m_ + 2)
                        * (&d__ * &sin).pow(&n_ + 1)
                        / (a__.pow(2)
                            * b__.pow(2)
                            * &d__
                            * &f__
                            * (&m_ + 1)
                            * (&m_ + 2))), x_)
                    - rubi_star(Atom::num(1)
                            / (a__.pow(2)
                                * b__.pow(2)
                                * (&m_ + 1)
                                * (&m_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3371,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) -
          Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(b^2*d*f*(m+n+4)) -
          1/(a*b^2*(m+1)*(m+n+4)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^n*
            Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2,0] && IntegersQ[2*m,2*n] && LtQ[m,-1] && Not[LtQ[n,-1]] && NeQ[m+n+4,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && ltq!(m_, -1)
                && !ltq!(n_, -1)
                && neq!(&m_ + &n_ + 4, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * (&n_ + 1) * (&n_ + 3)
                    - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 4)
                    + &a__ * &b__ * (&m_ + 1) * &sin
                    - (&a__.pow(2) * (&n_ + 2) * (&n_ + 3)
                        - &b__.pow(2) * (&m_ + &n_ + 3) * (&m_ + &n_ + 4))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&a__ + &b__ * &sin).pow(&m_ + 1) * (&d__ * &sin).pow(&n_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((a__.pow(2) - b__.pow(2))
                    * &cos
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    * (&d__ * &sin).pow(&n_ + 1)
                    / (&a__ * b__.pow(2) * &d__ * &f__ * (&m_ + 1))), x_)
                    - rubi_simp(&(&cos * (&a__ + &b__ * &sin).pow(&m_ + 2)
                        * (&d__ * &sin).pow(&n_ + 1)
                        / (b__.pow(2) * &d__ * &f__ * (&m_ + &n_ + 4))), x_)
                    - rubi_star(Atom::num(1)
                            / (&a__
                                * b__.pow(2)
                                * (&m_ + 1)
                                * (&m_ + &n_ + 4)), recursive)
        },
    ));
}

fn push_rules_rule_3372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3372,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) -
          b*(m+n+2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(a^2*d^2*f*(n+1)*(n+2)) -
          1/(a^2*d^2*(n+1)*(n+2)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+2)*
            Simp[a^2*n*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*m*Sin[e+f*x]-(a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,m},x] && NeQ[a^2-b^2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n]) && Not[m<-1] && LtQ[n,-1] && (LtQ[n,-2] || EqQ[m+n+4,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
                && !ltq!(m_, -1)
                && ltq!(n_, -1)
                && (ltq!(n_, -2) || eqq!(&m_ + &n_ + 4, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * &n_ * (&n_ + 2)
                    - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 3)
                    + &a__ * &b__ * &m_ * &sin
                    - (&a__.pow(2) * (&n_ + 1) * (&n_ + 2)
                        - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 4))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&a__ + &b__ * &sin).pow(&m_) * (&d__ * &sin).pow(&n_ + 2) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&cos * (&a__ + &b__ * &sin).pow(&m_ + 1) * (&d__ * &sin).pow(&n_ + 1)
                    / (&a__ * &d__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&(&b__
                        * (&m_ + &n_ + 2)
                        * &cos
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        * (&d__ * &sin).pow(&n_ + 2)
                        / (a__.pow(2) * d__.pow(2) * &f__ * (&n_ + 1) * (&n_ + 2))), x_)
                    - rubi_star(Atom::num(1)
                            / (a__.pow(2)
                                * d__.pow(2)
                                * (&n_ + 1)
                                * (&n_ + 2)), recursive)
        },
    ));
}

fn push_rules_rule_3373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3373,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) -
          Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) +
          1/(a*b*d*(n+1)*(m+n+4)) \\[Star] Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+1)*
            Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4)+a*b*(m+3)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,m},x] && NeQ[a^2-b^2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n]) && Not[m<-1] && LtQ[n,-1] && NeQ[m+n+4,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
                && !ltq!(m_, -1)
                && ltq!(n_, -1)
                && neq!(&m_ + &n_ + 4, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * (&n_ + 1) * (&n_ + 2)
                    - &b__.pow(2) * (&m_ + &n_ + 2) * (&m_ + &n_ + 4)
                    + &a__ * &b__ * (&m_ + 3) * &sin
                    - (&a__.pow(2) * (&n_ + 1) * (&n_ + 3)
                        - &b__.pow(2) * (&m_ + &n_ + 3) * (&m_ + &n_ + 4))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&a__ + &b__ * &sin).pow(&m_) * (&d__ * &sin).pow(&n_ + 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&cos * (&a__ + &b__ * &sin).pow(&m_ + 1) * (&d__ * &sin).pow(&n_ + 1)
                    / (&a__ * &d__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&(&cos * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        * (&d__ * &sin).pow(&n_ + 2)
                        / (&b__ * d__.pow(2) * &f__ * (&m_ + &n_ + 4))), x_)
                    + rubi_star(Atom::num(1)
                            / (&a__
                                * &b__
                                * &d__
                                * (&n_ + 1)
                                * (&m_ + &n_ + 4)), recursive)
        },
    ));
}

fn push_rules_rule_3374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3374,
        source: "Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a*(n+3)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(b^2*d*f*(m+n+3)*(m+n+4)) -
          Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(b*d^2*f*(m+n+4)) -
          1/(b^2*(m+n+3)*(m+n+4)) \\[Star] Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*
            Simp[a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4)+a*b*m*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+5))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n]) && Not[m<-1] && Not[LtQ[n,-1]] && NeQ[m+n+3,0] && NeQ[m+n+4,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
                && !ltq!(m_, -1)
                && !ltq!(n_, -1)
                && neq!(&m_ + &n_ + 3, 0)
                && neq!(&m_ + &n_ + 4, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(2) * (&n_ + 1) * (&n_ + 3)
                    - &b__.pow(2) * (&m_ + &n_ + 3) * (&m_ + &n_ + 4)
                    + &a__ * &b__ * &m_ * &sin
                    - (&a__.pow(2) * (&n_ + 2) * (&n_ + 3)
                        - &b__.pow(2) * (&m_ + &n_ + 3) * (&m_ + &n_ + 5))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&d__ * &sin).pow(&n_) * (&a__ + &b__ * &sin).pow(&m_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&a__ * (&n_ + 3) * &cos * (&d__ * &sin).pow(&n_ + 1)
                    * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (b__.pow(2) * &d__ * &f__ * (&m_ + &n_ + 3) * (&m_ + &n_ + 4))), x_)
                    - rubi_simp(&(&cos * (&d__ * &sin).pow(&n_ + 2)
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        / (&b__ * d__.pow(2) * &f__ * (&m_ + &n_ + 4))), x_)
                    - rubi_star(Atom::num(1)
                            / (b__.pow(2)
                                * (&m_ + &n_ + 3)
                                * (&m_ + &n_ + 4)), recursive)
        },
    ));
}

fn push_rules_rule_3375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3375,
        source: "Int[cos[e_.+f_.*x_]^6*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(n+1)) -
          b*(m+n+2)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(a^2*d^2*f*(n+1)*(n+2)) -
          a*(n+5)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+3)*(a+b*Sin[e+f*x])^(m+1)/(b^2*d^3*f*(m+n+5)*(m+n+6)) +
          Cos[e+f*x]*(d*Sin[e+f*x])^(n+4)*(a+b*Sin[e+f*x])^(m+1)/(b*d^4*f*(m+n+6)) +
          1/(a^2*b^2*d^2*(n+1)*(n+2)*(m+n+5)*(m+n+6)) \\[Star]
            Int[(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^m*
              Simp[a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(m+n+5)*(m+n+6)+b^4*(m+n+2)*(m+n+3)*(m+n+5)*(m+n+6) +
                a*b*m*(a^2*(n+1)*(n+2)-b^2*(m+n+5)*(m+n+6))*Sin[e+f*x] -
                (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(m+n+2)*(m+n+4)*(m+n+5)*(m+n+6)-a^2*b^2*(n+1)*(n+2)*(m+n+5)*(2*n+2*m+13))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2,0] && IntegersQ[2*m,2*n] && NeQ[n,-1] && NeQ[n,-2] && NeQ[m+n+5,0] && NeQ[m+n+6,0] && Not[IGtQ[m,0]]",
        desc: "Algebraic expansion and sine recurrence 3b with A\\[Rule]1,B\\[Rule]0,C\\[Rule]-3,m\\[Rule]n,n\\[Rule]p, 3b with A\\[Rule]-b (2+n+p),B\\[Rule]a (2+n-3 (1+n)),C\\[Rule]b (3+n+p),m\\[Rule]n+1,n\\[Rule]p, \\n\\t\\t\\t3a with A\\[Rule]3,B\\[Rule]0,C\\[Rule]-1,m\\[Rule]n+4,n\\[Rule]p and 3a with A\\[Rule]-a (4+n),B\\[Rule]b (-5-n-p+3 (6+n+p)),C\\[Rule]a (5+n),m\\[Rule]n+3,n\\[Rule]p",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(6)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_),
        with: [e__, f__, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && neq!(n_, -1)
                && neq!(n_, -2)
                && neq!(&m_ + &n_ + 5, 0)
                && neq!(&m_ + &n_ + 6, 0)
                && !igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let simp = rubi_simp(
                &(&a__.pow(4) * (&n_ + 1) * (&n_ + 2) * (&n_ + 3) * (&n_ + 5)
                    - &a__.pow(2)
                        * &b__.pow(2)
                        * (&n_ + 2)
                        * (Atom::num(2) * &n_ + 1)
                        * (&m_ + &n_ + 5)
                        * (&m_ + &n_ + 6)
                    + &b__.pow(4)
                        * (&m_ + &n_ + 2)
                        * (&m_ + &n_ + 3)
                        * (&m_ + &n_ + 5)
                        * (&m_ + &n_ + 6)
                    + &a__
                        * &b__
                        * &m_
                        * (&a__.pow(2) * (&n_ + 1) * (&n_ + 2)
                            - &b__.pow(2) * (&m_ + &n_ + 5) * (&m_ + &n_ + 6))
                        * &sin
                    - (&a__.pow(4) * (&n_ + 1) * (&n_ + 2) * (&n_ + 4) * (&n_ + 5)
                        + &b__.pow(4)
                            * (&m_ + &n_ + 2)
                            * (&m_ + &n_ + 4)
                            * (&m_ + &n_ + 5)
                            * (&m_ + &n_ + 6)
                        - &a__.pow(2)
                            * &b__.pow(2)
                            * (&n_ + 1)
                            * (&n_ + 2)
                            * (&m_ + &n_ + 5)
                            * (Atom::num(2) * &n_ + Atom::num(2) * &m_ + 13))
                        * sin.pow(2)),
                x_,
            );
            let recursive_integrand =
                (&d__ * &sin).pow(&n_ + 2) * (&a__ + &b__ * &sin).pow(&m_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&cos * (&d__ * &sin).pow(&n_ + 1) * (&a__ + &b__ * &sin).pow(&m_ + 1)
                    / (&a__ * &d__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&(&b__
                        * (&m_ + &n_ + 2)
                        * &cos
                        * (&d__ * &sin).pow(&n_ + 2)
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        / (a__.pow(2) * d__.pow(2) * &f__ * (&n_ + 1) * (&n_ + 2))), x_)
                    - rubi_simp(&(&a__ * (&n_ + 5) * &cos * (&d__ * &sin).pow(&n_ + 3)
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        / (b__.pow(2)
                            * d__.pow(3)
                            * &f__
                            * (&m_ + &n_ + 5)
                            * (&m_ + &n_ + 6))), x_)
                    + rubi_simp(&(&cos * (&d__ * &sin).pow(&n_ + 4)
                        * (&a__ + &b__ * &sin).pow(&m_ + 1)
                        / (&b__ * d__.pow(4) * &f__ * (&m_ + &n_ + 6))), x_)
                    + rubi_star(Atom::num(1)
                            / (a__.pow(2)
                                * b__.pow(2)
                                * d__.pow(2)
                                * (&n_ + 1)
                                * (&n_ + 2)
                                * (&m_ + &n_ + 5)
                                * (&m_ + &n_ + 6)), recursive)
        },
    ));
}

fn push_rules_rule_3376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3376,
        source: "Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[ExpandTrig[(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m*(1-sin[e+f*x]^2)^(p/2),x],x] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0] && IntegersQ[m,2*n,p/2] && (LtQ[m,-1] || EqQ[m,-1] && GtQ[p,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, Atom::num(2) * &n_, &p_ / 2])
                && (ltq!(m_, -1) || eqq!(m_, -1) && gtq!(p_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&d__ * i_sin(&angle)).pow(&n_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (Atom::num(1) - i_sin(&angle).pow(2)).pow(&p_ / 2);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3377,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p,sin[e+f*x]^n/(a+b*sin[e+f*x]),x],x] /;
        FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2,0] && IntegerQ[n] && (LtQ[n,0] || IGtQ[p+1/2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * i_sin(e__ + f__ * x_).pow(n_)
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, p_, n_, a__, b__, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(n_)
                && (ltq!(n_, 0) || igtq!(&p_ + Atom::num(1) / Atom::num(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let u = (&g__ * i_cos(&angle)).pow(&p_);
            let v = i_sin(&angle).pow(&n_) / (&a__ + &b__ * i_sin(&angle));
            let expanded = rubi_expand_trig_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3378,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g^2/a \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] -
          b*g^2/(a^2*d) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] -
          g^2*(a^2-b^2)/(a^2*d^2) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && GtQ[p,1] && (LeQ[n,-2] || EqQ[n,-3/2] && EqQ[p,3/2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && gtq!(p_, 1)
                && (leq!(n_, -2)
                    || eqq!(n_, -Atom::num(3) / Atom::num(2))
                        && eqq!(p_, Atom::num(3) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_ + 1)), x_);
            let recursive3 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2)
                    * scaled_sin.pow(&n_ + 2)
                    / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(g__.pow(2) / &a__, recursive1)
                    - rubi_star(&b__ * g__.pow(2) / (a__.pow(2) * &d__), recursive2)
                    - rubi_star(g__.pow(2) * (a__.pow(2) - b__.pow(2))
                            / (a__.pow(2) * d__.pow(2)), recursive3)
        },
    ));
}

fn push_rules_rule_3379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3379,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g^2/(a*b) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(b-a*Sin[e+f*x]),x] +
          g^2*(a^2-b^2)/(a*b*d) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && GtQ[p,1] && (LtQ[n,-1] || EqQ[p,3/2] && EqQ[n,-1/2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && gtq!(p_, 1)
                && (ltq!(n_, -1)
                    || eqq!(p_, Atom::num(3) / Atom::num(2))
                        && eqq!(n_, -Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_) * (&b__ - &a__ * angle.sin())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2)
                    * scaled_sin.pow(&n_ + 1)
                    / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(g__.pow(2) / (&a__ * &b__), recursive1) + rubi_star(g__.pow(2) * (a__.pow(2) - b__.pow(2))
                        / (&a__ * &b__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3380,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g^2/b^2 \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] -
          g^2*(a^2-b^2)/b^2 \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && GtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_) * (&a__ - &b__ * angle.sin())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_) / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(g__.pow(2) / b__.pow(2), recursive1)
                    - rubi_star(g__.pow(2) * (a__.pow(2) - b__.pow(2))
                            / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3381,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a*d^2/(a^2-b^2) \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-2),x] -
          b*d/(a^2-b^2) \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1),x] -
          a^2*d^2/(g^2*(a^2-b^2)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^(n-2)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && LtQ[p,-1] && GtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(p_, -1)
                && gtq!(n_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ - 2)), x_);
            let recursive2 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ - 1)), x_);
            let recursive3 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ + 2) * scaled_sin.pow(&n_ - 2) / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(&a__ * d__.pow(2) / (a__.pow(2) - b__.pow(2)), recursive1) - rubi_star(&b__ * &d__ / (a__.pow(2) - b__.pow(2)), recursive2) - rubi_star(a__.pow(2) * d__.pow(2)
                        / (g__.pow(2) * (a__.pow(2) - b__.pow(2))), recursive3)
        },
    ));
}

fn push_rules_rule_3382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3382,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -d/(a^2-b^2) \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1)*(b-a*Sin[e+f*x]),x] +
          a*b*d/(g^2*(a^2-b^2)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^(n-1)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && LtQ[p,-1] && GtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(p_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 = rubi_rhs_int(
                &(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ - 1) * (&b__ - &a__ * angle.sin())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ + 2)
                    * scaled_sin.pow(&n_ - 1)
                    / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(-&d__ / (a__.pow(2) - b__.pow(2)), recursive1) + rubi_star(&a__ * &b__ * &d__
                        / (g__.pow(2) * (a__.pow(2) - b__.pow(2))), recursive2)
        },
    ));
}

fn push_rules_rule_3383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3383,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          1/(a^2-b^2) \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] -
          b^2/(g^2*(a^2-b^2)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && LtQ[p,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 = rubi_rhs_int(
                &(scaled_cos.pow(&p_) * scaled_sin.pow(&n_) * (&a__ - &b__ * angle.sin())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ + 2) * scaled_sin.pow(&n_) / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(Atom::num(1) / (a__.pow(2) - b__.pow(2)), recursive1) - rubi_star(b__.pow(2)
                        / (g__.pow(2) * (a__.pow(2) - b__.pow(2))), recursive2)
        },
    ));
}

fn push_rules_rule_3384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3384,
        source: "Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          -4*Sqrt[2]*g/f \\[Star] Subst[Int[x^2/(((a+b)*g^2+(a-b)*x^4)*Sqrt[1-x^4/g^2]),x],x,Sqrt[g*Cos[e+f*x]]/Sqrt[1+Sin[e+f*x]]] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).sqrt()
            / (i_sin(e__ + f__ * x_).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(2)
                / (((&a__ + &b__) * g__.pow(2) + (&a__ - &b__) * z.pow(4))
                    * (Atom::num(1) - z.pow(4) / g__.pow(2)).sqrt());
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = (&g__ * angle.cos()).sqrt() / (Atom::num(1) + angle.sin()).sqrt();

            let substituted = rubi_subst(&primitive, sub, replacement);

            rubi_star(-Atom::num(4) * Atom::num(2).sqrt() * &g__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3385,
        source: "Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(Sqrt[d_*sin[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]] \\[Star] Int[Sqrt[g*Cos[e+f*x]]/(Sqrt[Sin[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).sqrt()
            / ((d__ * i_sin(e__ + f__ * x_)).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [g__, e__, f__, d__, a__, b__, x_],
        optional: [g__, e__, f__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&g__ * angle.cos()).sqrt() / (angle.sin().sqrt() * (&a__ + &b__ * angle.sin()));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.sin().sqrt() / (&d__ * angle.sin()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3386,
        source: "Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(Sqrt[cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          With[{q=Rt[-a^2+b^2,2]},
          2*Sqrt[2]*d*(b+q)/(f*q) \\[Star] Subst[Int[1/((d*(b+q)+a*x^2)*Sqrt[1-x^4/d^2]),x],x,Sqrt[d*Sin[e+f*x]]/Sqrt[1+Cos[e+f*x]]] -
          2*Sqrt[2]*d*(b-q)/(f*q) \\[Star] Subst[Int[1/((d*(b-q)+a*x^2)*Sqrt[1-x^4/d^2]),x],x,Sqrt[d*Sin[e+f*x]]/Sqrt[1+Cos[e+f*x]]]] /;
        FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution and algebraic expansion",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).sqrt()
            / (i_cos(e__ + f__ * x_).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [d__, e__, f__, a__, b__, x_],
        optional: [d__, e__, f__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(-a__.pow(2) + b__.pow(2)), 2);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed1 = Atom::num(1)
                / ((&d__ * (&b__ + &q) + &a__ * z.pow(2))
                    * (Atom::num(1) - z.pow(4) / d__.pow(2)).sqrt());
            let primitive1 = rubi_rhs_int(&transformed1, sub);
            let transformed2 = Atom::num(1)
                / ((&d__ * (&b__ - &q) + &a__ * z.pow(2))
                    * (Atom::num(1) - z.pow(4) / d__.pow(2)).sqrt());
            let primitive2 = rubi_rhs_int(&transformed2, sub);
            let angle = &e__ + &f__ * x_;
            let replacement = (&d__ * angle.sin()).sqrt() / (Atom::num(1) + angle.cos()).sqrt();

            let substituted1 = rubi_subst(&primitive1, sub, &replacement);
            let substituted2 = rubi_subst(&primitive2, sub, replacement);

            rubi_star(Atom::num(2) * Atom::num(2).sqrt() * &d__ * (&b__ + &q)
                        / (&f__ * &q), substituted1) - rubi_star(Atom::num(2) * Atom::num(2).sqrt() * &d__ * (&b__ - &q)
                        / (&f__ * &q), substituted2)
        },
    ));
}

fn push_rules_rule_3387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3387,
        source: "Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          Sqrt[Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]] \\[Star] Int[Sqrt[d*Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * i_sin(e__ + f__ * x_)).sqrt()
            / ((g__ * i_cos(e__ + f__ * x_)).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [d__, e__, f__, g__, a__, b__, x_],
        optional: [d__, e__, f__, g__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&d__ * angle.sin()).sqrt() / (angle.cos().sqrt() * (&a__ + &b__ * angle.sin()));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.cos().sqrt() / (&g__ * angle.cos()).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3388,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          d/b \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1),x] -
          a*d/b \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && LtQ[-1,p,1] && GtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(-1, p_, 1)
                && gtq!(n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ - 1)), x_);
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ - 1) / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(&d__ / &b__, recursive1)
                    - rubi_star(&a__ * &d__ / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3389,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n,x] -
          b/(a*d) \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*n,2*p] && LtQ[-1,p,1] && LtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(-1, p_, 1)
                && ltq!(n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 = rubi_rhs_int(&(scaled_cos.pow(&p_) * scaled_sin.pow(&n_)), x_);
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ + 1) / (&a__ + &b__ * angle.sin())),
                x_,
            );

            rubi_star(Atom::num(1) / &a__, recursive1)
                    - rubi_star(&b__ / (&a__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3390,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          2*a*b/d \\[Star] Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1),x] +
          Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n*(a^2+b^2*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(2),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sin = &d__ * angle.sin();
            let recursive1 =
                rubi_rhs_int(&(scaled_cos.pow(&p_) * scaled_sin.pow(&n_ + 1)), x_);
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_) * scaled_sin.pow(&n_) * (a__.pow(2) + b__.pow(2) * angle.sin().pow(2))),
                x_,
            );

            rubi_star(Atom::num(2) * &a__ * &b__ / &d__, recursive1) + recursive2
        },
    ));
}

fn push_rules_rule_3391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3391,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
        FreeQ[{a,b,d,e,f,g,n,p},x] && NeQ[a^2-b^2,0] && IntegerQ[m] && (GtQ[m,0] || IntegerQ[n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__, n_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && (gtq!(m_, 0) || integerq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let u = (&g__ * i_cos(&angle)).pow(&p_);
            let v = (&d__ * i_sin(&angle)).pow(&n_) * (&a__ + &b__ * i_sin(&angle)).pow(&m_);
            let expanded = rubi_expand_trig_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3392,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g^2/a \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1),x] -
          b*g^2/(a^2*d) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1),x] -
          g^2*(a^2-b^2)/(a^2*d^2) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[m,2*n,2*p] && LtQ[m,0] && GtQ[p,1] && (LeQ[n,-2] || EqQ[m,-1] && EqQ[n,-3/2] && EqQ[p,3/2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, d__, n_, a__, b__, m_, x_],
        optional: [g__, e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, d__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
                && ltq!(m_, 0)
                && gtq!(p_, 1)
                && (leq!(n_, -2)
                    || eqq!(m_, -1)
                        && eqq!(n_, -Atom::num(3) / Atom::num(2))
                        && eqq!(p_, Atom::num(3) / Atom::num(2)))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let scaled_sin = &d__ * i_sin(&angle);
            let affine = &a__ + &b__ * i_sin(&angle);
            let recursive1 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_) * affine.pow(&m_ + 1)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_ + 1) * affine.pow(&m_ + 1)),
                x_,
            );
            let recursive3 = rubi_rhs_int(
                &(scaled_cos.pow(&p_ - 2) * scaled_sin.pow(&n_ + 2) * affine.pow(&m_)),
                x_,
            );

            rubi_star(g__.pow(2) / &a__, recursive1)
                    - rubi_star(&b__ * g__.pow(2) / (a__.pow(2) * &d__), recursive2)
                    - rubi_star(g__.pow(2) * (a__.pow(2) - b__.pow(2))
                            / (a__.pow(2) * d__.pow(2)), recursive3)
        },
    ));
}

fn push_rules_rule_3393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3393,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^(2*m) \\[Star] Int[(c+d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[a^2-b^2,0] && IntegersQ[m,p] && EqQ[2*m+p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, p_])
                && eqq!(Atom::num(2) * &m_ + &p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand =
                (&c__ + &d__ * angle.sin()).pow(&n_) / (&a__ - &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3394,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (a/g)^(2*m) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[a^2-b^2,0] && IntegerQ[m] && (EqQ[2*m+p,0] || GtQ[2*m+p,0] && LtQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && (eqq!(Atom::num(2) * &m_ + &p_, 0)
                    || gtq!(Atom::num(2) * &m_ + &p_, 0) && ltq!(p_, -1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);
            let recursive_integrand = scaled_cos.pow(Atom::num(2) * &m_ + &p_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                / (&a__ - &b__ * i_sin(&angle)).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ / &g__).pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3395,
        source: "Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          1/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && IntegersQ[2*m,2*n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, f__, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_ + 1)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * (&a__ - &b__ * angle.sin());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3396,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]]) \\[Star]
            Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && EqQ[a^2-b^2,0] && IntegerQ[p/2] && IntegerQ[m]",
        desc: "Algebraic expansion, piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&p_ / 2)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (Atom::num(1) + &b__ * &z / &a__).pow(&m_ + (&p_ - 1) / 2)
                * (Atom::num(1) - &b__ * &z / &a__).pow((&p_ - 1) / 2)
                * (&c__ + &d__ * &z).pow(&n_);
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

fn push_rules_rule_3397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3397,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Cos[e+f*x]/(a^(p-2)*f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]) \\[Star]
            Subst[Int[(a+b*x)^(m+p/2-1/2)*(a-b*x)^(p/2-1/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[a^2-b^2,0] && IntegerQ[p/2] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&p_ / 2)
                && !integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_ + &p_ / 2 - Atom::num(1) / Atom::num(2))
                * (&a__ - &b__ * &z).pow(&p_ / 2 - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, angle.sin());
            rubi_star(angle.cos()
                    / (a__.pow(&p_ - 2)
                        * &f__
                        * (&a__ + &b__ * angle.sin()).sqrt()
                        * (&a__ - &b__ * angle.sin()).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3398,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p,(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[a^2-b^2,0] && IGtQ[m,0] && (IntegerQ[p] || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
                && (integerq!(p_) || igtq!(n_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let u = (&g__ * i_cos(&angle)).pow(&p_);
            let v = (&a__ + &b__ * i_sin(&angle)).pow(&m_) * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3399,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^m*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2)) \\[Star]
            Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[a^2-b^2,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (Atom::num(1) + &b__ * &z / &a__).pow(&m_ + (&p_ - 1) / 2)
                * (Atom::num(1) - &b__ * &z / &a__).pow((&p_ - 1) / 2)
                * (&c__ + &d__ * &z).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));
            rubi_star(a__.pow(&m_) * &g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (Atom::num(1) + i_sin(&angle)).pow((&p_ - 1) / 2)
                        * (Atom::num(1) - i_sin(&angle)).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3400,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)/(f*(a+b*Sin[e+f*x])^((p-1)/2)*(a-b*Sin[e+f*x])^((p-1)/2)) \\[Star]
            Subst[Int[(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&a__ + &b__ * &z).pow(&m_ + (&p_ - 1) / 2)
                * (&a__ - &b__ * &z).pow((&p_ - 1) / 2)
                * (&c__ + &d__ * &z).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * i_cos(&angle);

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));
            rubi_star(&g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (&a__ + &b__ * i_sin(&angle)).pow((&p_ - 1) / 2)
                        * (&a__ - &b__ * i_sin(&angle)).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3401(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3401,
        source: "Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(1-Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[a^2-b^2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, f__, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                * (Atom::num(1) - angle.sin().pow(2));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3402(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3402,
        source: "Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[ExpandTrig[(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n*(1-sin[e+f*x]^2)^(p/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[a^2-b^2,0] && IGtQ[p/2,0] && (IGtQ[m,0] || IntegersQ[2*m,2*n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(&p_ / 2, 0)
                && (igtq!(m_, 0) || integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_)
                * (Atom::num(1) - i_sin(&angle).pow(2)).pow(&p_ / 2);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3403(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3403,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[ExpandTrig[(g*cos[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2,0] && IntegersQ[2*m,2*n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&g__ * i_cos(&angle)).pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3404(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3404,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[a^2-b^2,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let integrand = (&g__ * angle.cos()).pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&c__ + &d__ * angle.sin()).pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3405(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3405,
        source: "Int[(g_.*sec[e_.+f_.*x_])^p_*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^(2*IntPart[p])*(g*Cos[e+f*x])^FracPart[p]*(g*Sec[e+f*x])^FracPart[p] \\[Star]
            Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(g*Cos[e+f*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, a__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.sin()).pow(&m_)
                * (&c__ + &d__ * angle.sin()).pow(&n_)
                / (&g__ * angle.cos()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(Atom::num(2) * rubi_int_part(&p_))
                    * (&g__ * angle.cos()).pow(rubi_frac_part(&p_))
                    * (&g__ * angle.sec()).pow(rubi_frac_part(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_3406(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3406,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^(2*IntPart[p])*(g*Sin[e+f*x])^FracPart[p]*(g*Csc[e+f*x])^FracPart[p] \\[Star]
            Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(g*Sin[e+f*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_csc(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_cos(e__ + f__ * x_)).pow(n_),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, a__, b__, m_, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = (&a__ + &b__ * angle.cos()).pow(&m_)
                * (&c__ + &d__ * angle.cos()).pow(&n_)
                / (&g__ * angle.sin()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(Atom::num(2) * rubi_int_part(&p_))
                    * (&g__ * angle.sin()).pow(rubi_frac_part(&p_))
                    * (&g__ * angle.csc()).pow(rubi_frac_part(&p_)), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3312_through_3342_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3312..=3342).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3312..=3342).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3343_through_3392_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3343..=3392).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3343..=3392).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3393_through_3406_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3393..=3406).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3393..=3406).collect::<Vec<_>>());
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
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let w_ = symbols.w_;
    (g__ * i_cos(e__ + f__ * w_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * w_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * w_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        / (d__ * i_sin(e__ + f__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_)
        * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_) * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        / (a__ + b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_)
        * i_sin(e__ + f__ * x_).pow(2)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(2)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(2)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(2)
        * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(4)
        * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(p_)
        * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}
