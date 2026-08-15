use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2771(rules);
    push_rules_rule_2772(rules);
    push_rules_rule_2780(rules);
    push_rules_rule_2781(rules);
    push_rules_rule_2782(rules);
    push_rules_rule_2783(rules);
    push_rules_rule_2798(rules);
}

fn push_rules_rule_2771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2771,
        source: "Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^r)^q,x]},
          u*(a+b*Log[c*x^n]) - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [m_, e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && igtq!(q_, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let base_power = x_.pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base_power, x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_) - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2772,
        source: "Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^r)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0] && IntegerQ[m] && Not[EqQ[q,1] && EqQ[m,-1]]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [m_, e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && igtq!(q_, 0)
                && integerq!(m_)
                && !(eqq!(q_, 1) && eqq!(m_, -1))
        },
        rhs: {
            let base_power = x_.pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base_power, x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u) - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2780,
        source: "Int[x_^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_^r_.),x_Symbol] :=
          1/d \\[Star] Int[x^m*(a+b*Log[c*x^n])^p,x] -
          e/d \\[Star] Int[(x^(m+r)*(a+b*Log[c*x^n])^p)/(d+e*x^r),x] /;
        FreeQ[{a,b,c,d,e,m,n,r},x] && IGtQ[p,0] && IGtQ[r,0] && ILtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / (d__ + e__ * x_.pow(r_)),
        with: [m_, a__, b__, c__, n_, p_, d__, e__, r_, x_],
        optional: [m_, a__, b__, c__, n_, p_, e__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, r_], x_)
                && igtq!(p_, 0)
                && igtq!(r_, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand_1 = x_.pow(&m_) * logarithmic.pow(&p_);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 =
                x_.pow(&m_ + &r_) * logarithmic.pow(&p_) / (&d__ + &e__ * x_.pow(&r_));
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_star(Atom::num(1) / &d__, recursive_1) - rubi_star(e__, recursive_2 / &d__)
        },
    ));
}

fn push_rules_rule_2781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2781,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/(d*f*(q+1)) +
          b*n*p/(d*(q+1)) \\[Star] Int[(f*x)^m*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[m+q+2,0] && IGtQ[p,0] && LtQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_], x_)
                && eqq!(&m_ + &q_ + 2, 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &d__ * &f__ * (&q_ + 1);
            let recursive_denominator = &d__ * (&q_ + 1);
            let recursive_integrand =
                scaled.pow(&m_) * base.pow(&q_ + 1) * logarithmic.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled.pow(&m_ + 1) * base.pow(&q_ + 1) * logarithmic.pow(&p_) / denominator), x_)
                    + rubi_star(&b__ * &n_ * &p_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2782,
        source: "Int[x_^m_.*(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,n},x] && ILtQ[m+q+2,0] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [m_, d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && iltq!(&m_ + &q_ + 2, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let base_power = x_.pow(&m_) * (&d__ + &e__ * x_).pow(&q_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base_power, x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u) - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2783,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/(d*f*(q+1)) +
          (m+q+2)/(d*(q+1)) \\[Star] Int[(f*x)^m*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p,x] +
          b*n*p/(d*(q+1)) \\[Star] Int[(f*x)^m*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && ILtQ[m+q+2,0] && IGtQ[p,0] && LtQ[q,-1] && GtQ[m,0]",
        desc: "Algebraic expansion and integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, e__, a__, b__, c__, n_, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && iltq!(&m_ + &q_ + 2, 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &d__ * &f__ * (&q_ + 1);
            let recursive_denominator = &d__ * (&q_ + 1);
            let recursive_integrand_1 = scaled.pow(&m_) * base.pow(&q_ + 1) * logarithmic.pow(&p_);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 =
                scaled.pow(&m_) * base.pow(&q_ + 1) * logarithmic.pow(&p_ - 1);
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(&(-scaled.pow(&m_ + 1) * base.pow(&q_ + 1) * logarithmic.pow(&p_) / denominator), x_)
                    + rubi_star(&m_ + &q_ + 2, recursive_1 / &recursive_denominator)
                    + rubi_star(&b__ * &n_ * &p_ / recursive_denominator, recursive_2)
        },
    ));
}

fn push_rules_rule_2798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2798,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (f+g*x)^(m+1)*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/((q+1)*(e*f-d*g)) -
          b*n*p/((q+1)*(e*f-d*g)) \\[Star] Int[(f+g*x)^(m+1)*(d+e*x)^(q+1)*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && NeQ[e*f-d*g,0] && EqQ[m+q+2,0] && IGtQ[p,0] && LtQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (d__ + e__ * x_).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [f__, g__, m_, d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_, p_],
        when: {
            let determinant = &e__ * &f__ - &d__ * &g__;

            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_], x_)
                && neq!(determinant, 0)
                && eqq!(&m_ + &q_ + 2, 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let determinant = &e__ * &f__ - &d__ * &g__;
            let left_base = &f__ + &g__ * x_;
            let right_base = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = (&q_ + 1) * &determinant;
            let recursive_integrand = left_base.pow(&m_ + 1)
                * right_base.pow(&q_ + 1)
                * logarithmic.pow(&p_ - 1)
                / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(left_base.pow(&m_ + 1)
                        * right_base.pow(&q_ + 1)
                        * logarithmic.pow(&p_)
                        / &denominator),
                    x_,
                ) - rubi_star(&b__ * &n_ * &p_ / denominator, recursive)
        },
    ));
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
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log())
}
