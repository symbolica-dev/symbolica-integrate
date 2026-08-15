use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2607(rules);
    push_rules_rule_2608(rules);
    push_rules_rule_2609(rules);
    push_rules_rule_2610(rules);
    push_rules_rule_2611(rules);
    push_rules_rule_2612(rules);
    push_rules_rule_2613(rules);
    push_rules_rule_2614(rules);
    push_rules_rule_2615(rules);
    push_rules_rule_2616(rules);
    push_rules_rule_2617(rules);
    push_rules_rule_2618(rules);
    push_rules_rule_2619(rules);
}

fn push_rules_rule_2607(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, b__, c__, d__, m_, n_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2607,
        source: "Int[(c_.+d_.*x_)^m_.*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_.,x_Symbol] :=
          (c+d*x)^m*(b*F^(g*(e+f*x)))^n/(f*g*n*Log[F]) -
          d*m/(f*g*n*Log[F]) \\[Star] Int[(c+d*x)^(m-1)*(b*F^(g*(e+f*x)))^n,x] /;
        FreeQ[{F,b,c,d,e,f,g,n},x] && GtQ[m,0] && IntegerQ[2*m] && Not[TrueQ[$UseGamma]]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, b__, capital_f_, g__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_],
        when: {
            freeq!([capital_f_, b__, c__, d__, e__, f__, g__, n_], x_)
                && gtq!(m_, 0)
                && integerq!(2 * &m_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = (&b__ * capital_f_.pow(&g__ * (&e__ + &f__ * x_))).pow(&n_);
            let denominator = &f__ * &g__ * &n_ * capital_f_.log();
            let recursive_integrand = affine.pow(&m_ - 1) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&m_) * &exponential / &denominator),
                    x_,
                ) - rubi_star(&d__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2608(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, b__, c__, d__, m_, n_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2608,
        source: "Int[(c_.+d_.*x_)^m_*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_.,x_Symbol] :=
          (c+d*x)^(m+1)*(b*F^(g*(e+f*x)))^n/(d*(m+1)) -
          f*g*n*Log[F]/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*(b*F^(g*(e+f*x)))^n,x] /;
        FreeQ[{F,b,c,d,e,f,g,n},x] && LtQ[m,-1] && IntegerQ[2*m] && Not[TrueQ[$UseGamma]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, b__, capital_f_, g__, e__, f__, n_, x_],
        optional: [c__, d__, b__, g__, e__, f__, n_],
        when: {
            freeq!([capital_f_, b__, c__, d__, e__, f__, g__, n_], x_)
                && ltq!(m_, -1)
                && integerq!(2 * &m_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = (&b__ * capital_f_.pow(&g__ * (&e__ + &f__ * x_))).pow(&n_);
            let denominator = &d__ * (&m_ + 1);
            let recursive_integrand = affine.pow(&m_ + 1) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&m_ + 1) * &exponential / &denominator),
                    x_,
                ) - rubi_star(&f__ * &g__ * &n_ * capital_f_.log() / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2609(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, c__, d__, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2609,
        source: "Int[F_^(g_.*(e_.+f_.*x_))/(c_.+d_.*x_),x_Symbol] :=
          F^(g*(e-c*f/d))/d*ExpIntegralEi[f*g*(c+d*x)*Log[F]/d] /;
        FreeQ[{F,c,d,e,f,g},x] && Not[TrueQ[$UseGamma]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(g__ * (e__ + f__ * x_)) / (c__ + d__ * x_),
        with: [capital_f_, g__, e__, f__, c__, d__, x_],
        optional: [g__, e__, f__, c__, d__],
        when: {
            freeq!([capital_f_, c__, d__, e__, f__, g__], x_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exp_integral_argument = &f__ * &g__ * &affine * capital_f_.log() / &d__;

            rubi_simp(
                &(capital_f_.pow(&g__ * (&e__ - &c__ * &f__ / &d__))
                    * rubi_exp_integral_ei(exp_integral_argument)
                    / &d__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2610(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, c__, d__, m_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2610,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(g_.*(e_.+f_.*x_)),x_Symbol] :=
          (-d)^m*F^(g*(e-c*f/d))/(f^(m+1)*g^(m+1)*Log[F]^(m+1))*Gamma[m+1,-f*g*Log[F]/d*(c+d*x)] /;
        FreeQ[{F,c,d,e,f,g},x] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, capital_f_, g__, e__, f__, x_],
        optional: [c__, d__, m_, g__, e__, f__],
        when: {
            freeq!([capital_f_, c__, d__, e__, f__, g__], x_)
                && integerq!(m_)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let log_f = capital_f_.log();
            let denominator = f__.pow(&m_ + 1) * g__.pow(&m_ + 1) * log_f.pow(&m_ + 1);
            let gamma_argument = -&f__ * &g__ * &log_f * &affine / &d__;

            rubi_simp(
                &((-&d__).pow(&m_)
                    * capital_f_.pow(&g__ * (&e__ - &c__ * &f__ / &d__))
                    * rubi_gamma(&m_ + 1, gamma_argument)
                    / denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2611(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, c__, d__, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2611,
        source: "Int[F_^(g_.*(e_.+f_.*x_))/Sqrt[c_.+d_.*x_],x_Symbol] :=
          2/d \\[Star] Subst[Int[F^(g*(e-c*f/d)+f*g*x^2/d),x],x,Sqrt[c+d*x]] /;
        FreeQ[{F,c,d,e,f,g},x] && Not[TrueQ[$UseGamma]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: capital_f_.pow(g__ * (e__ + f__ * x_)) / (c__ + d__ * x_).sqrt(),
        with: [capital_f_, g__, e__, f__, c__, d__, x_],
        optional: [g__, e__, f__, c__, d__],
        when: {
            freeq!([capital_f_, c__, d__, e__, f__, g__], x_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                capital_f_.pow(&g__ * (&e__ - &c__ * &f__ / &d__) + &f__ * &g__ * sub_atom.pow(2) / &d__);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substitution = (&c__ + &d__ * x_).sqrt();

            rubi_star(Atom::num(2), rubi_subst(&transformed, sub, substitution) / &d__)
        },
    ));
}

fn push_rules_rule_2612(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, c__, d__, m_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2612,
        source: "Int[(c_.+d_.*x_)^m_*F_^(g_.*(e_.+f_.*x_)),x_Symbol] :=
          -F^(g*(e-c*f/d))*(c+d*x)^FracPart[m]/(d*(-f*g*Log[F]/d)^(IntPart[m]+1)*(-f*g*Log[F]*(c+d*x)/d)^FracPart[m])*
            Gamma[m+1,(-f*g*Log[F]/d)*(c+d*x)] /;
        FreeQ[{F,c,d,e,f,g,m},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, capital_f_, g__, e__, f__, x_],
        optional: [c__, d__, g__, e__, f__],
        when: {
            freeq!([capital_f_, c__, d__, e__, f__, g__, m_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let log_f = capital_f_.log();
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let scaled_log = -&f__ * &g__ * &log_f / &d__;
            let scaled_affine_log = -&f__ * &g__ * &log_f * &affine / &d__;
            let denominator = &d__ * scaled_log.pow(&int_m + 1) * scaled_affine_log.pow(&frac_m);

            rubi_simp(
                &(-capital_f_.pow(&g__ * (&e__ - &c__ * &f__ / &d__))
                    * affine.pow(&frac_m)
                    * rubi_gamma(&m_ + 1, scaled_log * &affine)
                    / denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2613(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, b__, c__, d__, m_, n_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2613,
        source: "Int[(c_.+d_.*x_)^m_.*(b_.*F_^(g_.*(e_.+f_.*x_)))^n_,x_Symbol] :=
          (b*F^(g*(e+f*x)))^n/F^(g*n*(e+f*x)) \\[Star] Int[(c+d*x)^m*F^(g*n*(e+f*x)),x] /;
        FreeQ[{F,b,c,d,e,f,g,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, b__, capital_f_, g__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__],
        when: { freeq!([capital_f_, b__, c__, d__, e__, f__, g__, m_, n_], x_) },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponent_argument = &g__ * (&e__ + &f__ * x_);
            let exponential = (&b__ * capital_f_.pow(&exponent_argument)).pow(&n_);
            let recursive_integrand = affine.pow(&m_) * capital_f_.pow(&g__ * &n_ * (&e__ + &f__ * x_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(exponential, recursive
                    / capital_f_.pow(&g__ * &n_ * (&e__ + &f__ * x_)))
        },
    ));
}

fn push_rules_rule_2614(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__
    );
    rules.push(rubi_rule!(
        order: 2614,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c+d*x)^m,(a+b*(F^(g*(e+f*x)))^n)^p,x],x] /;
        FreeQ[{F,a,b,c,d,e,f,g,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, e__, f__, n_, p_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let affine_power = (&c__ + &d__ * x_).pow(&m_);
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let binomial_power = (&a__ + &b__ * exponential).pow(&p_);
            let expanded = rubi_expand_integrand_product(&affine_power, &binomial_power, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2615(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__);
    rules.push(rubi_rule!(
        order: 2615,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.),x_Symbol] :=
          (c+d*x)^(m+1)/(a*d*(m+1)) - b/a \\[Star] Int[(c+d*x)^m*(F^(g*(e+f*x)))^n/(a+b*(F^(g*(e+f*x)))^n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) / (a__ + b__ * capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_)),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && igtq!(m_, 0)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let binomial = &a__ + &b__ * &exponential;
            let recursive_integrand = affine.pow(&m_) * exponential / binomial;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let first = rubi_simp(
                &(affine.pow(&m_ + 1) / (&a__ * &d__ * (&m_ + 1))),
                x_,
            );
            let second = rubi_simp(&(&b__ * recursive / &a__), x_);

            rubi_simp(&(first), x_) - rubi_star(Atom::num(1), second)
        },
    ));
}

fn push_rules_rule_2616(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__
    );
    rules.push(rubi_rule!(
        order: 2616,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_,x_Symbol] :=
          1/a \\[Star] Int[(c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^(p+1),x] -
          b/a \\[Star] Int[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && ILtQ[p,0] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, e__, f__, n_, p_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && iltq!(p_, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let binomial = &a__ + &b__ * &exponential;
            let first_integrand = affine.pow(&m_) * binomial.pow(&p_ + 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = affine.pow(&m_) * exponential * binomial.pow(&p_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(b__, second / &a__)
        },
    ));
}

fn push_rules_rule_2617(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__
    );
    rules.push(rubi_rule!(
        order: 2617,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_,x_Symbol] :=
          With[{u=IntHide[(a+b*(F^(g*(e+f*x)))^n)^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, e__, f__, n_, p_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && igtq!(m_, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let binomial = &a__ + &b__ * exponential;
            let u = rubi_int_hide(&binomial.pow(&p_), x_).rubi_rhs();
            let recursive_integrand = affine.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(affine.pow(&m_), u)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_2618(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, g__, m_, n_, p_, v__, x_);
    rules.push(rubi_rule!(
        order: 2618,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*(F_^(g_.*v_))^n_.)^p_.,x_Symbol] :=
          Int[(c+d*x)^m*(a+b*(F^(g*ExpandToSum[v,x]))^n)^p,x] /;
        FreeQ[{F,a,b,c,d,g,n,p},x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_)
            * (a__ + b__ * capital_f_.pow(g__ * v__).pow(n_)).pow(p_),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, v__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, g__, n_, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, g__, n_, p_], x_)
                && rubi_linear_q(&v__, x_)
                && !rubi_linear_match_q(&v__, x_)
                && integerq!(m_)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let integrand = (&c__ + &d__ * x_).pow(&m_)
                * (&a__ + &b__ * capital_f_.pow(&g__ * expanded_v).pow(&n_)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2619(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__
    );
    rules.push(rubi_rule!(
        order: 2619,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, capital_f_, g__, e__, f__, n_, p_, x_],
        optional: [c__, d__, m_, b__, g__, e__, f__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&c__ + &d__ * x_).pow(&m_)
                * (&a__ + &b__ * capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_)).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (b__ * capital_f_.pow(g__ * (e__ + f__ * x_))).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * capital_f_.pow(g__ * (e__ + f__ * x_))
}
