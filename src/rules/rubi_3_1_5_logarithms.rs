use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2799(rules);
    push_rules_rule_2770(rules);
    push_rules_rule_2800(rules);
    push_rules_rule_2801(rules);
    push_rules_rule_2773(rules);
    push_rules_rule_2774(rules);
    push_rules_rule_2775(rules);
    push_rules_rule_2776(rules);
    push_rules_rule_2777(rules);
    push_rules_rule_2784(rules);
    push_rules_rule_2785(rules);
    push_rules_rule_2786(rules);
    push_rules_rule_2787(rules);
    push_rules_rule_2778(rules);
    push_rules_rule_2802(rules);
    push_rules_rule_2779(rules);
    push_rules_rule_2788(rules);
    push_rules_rule_2789(rules);
    push_rules_rule_2790(rules);
    push_rules_rule_2791(rules);
    push_rules_rule_2792(rules);
    push_rules_rule_2793(rules);
    push_rules_rule_2794(rules);
    push_rules_rule_2795(rules);
    push_rules_rule_2796(rules);
    push_rules_rule_2797(rules);
    push_rules_rule_2803(rules);
    push_rules_rule_2804(rules);
    push_rules_rule_2805(rules);
    push_rules_rule_2806(rules);
    push_rules_rule_2807(rules);
    push_rules_rule_2808(rules);
    push_rules_rule_2809(rules);
    push_rules_rule_2810(rules);
    push_rules_rule_2811(rules);
    push_rules_rule_2812(rules);
    push_rules_rule_2813(rules);
    push_rules_rule_2814(rules);
    push_rules_rule_2815(rules);
    push_rules_rule_2816(rules);
    push_rules_rule_2817(rules);
    push_rules_rule_2818(rules);
    push_rules_rule_2819(rules);
    push_rules_rule_2820(rules);
    push_rules_rule_2821(rules);
    push_rules_rule_2822(rules);
    push_rules_rule_2823(rules);
    push_rules_rule_2824(rules);
    push_rules_rule_2825(rules);
    push_rules_rule_2826(rules);
    push_rules_rule_2827(rules);
    push_rules_rule_2828(rules);
    push_rules_rule_2829(rules);
    push_rules_rule_2830(rules);
    push_rules_rule_2831(rules);
    push_rules_rule_2832(rules);
    push_rules_rule_2833(rules);
    push_rules_rule_2834(rules);
    push_rules_rule_2835(rules);
}

fn push_rules_rule_2799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2799,
        source: "Int[(A_.+B_.*Log[c_.*(d_.+e_.*x_)^n_.])/Sqrt[a_+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
          B*(d+e*x)*Sqrt[a+b*Log[c*(d+e*x)^n]]/(b*e) +
          (2*A*b-B*(2*a+b*n))/(2*b) \\[Star] Int[1/Sqrt[a+b*Log[c*(d+e*x)^n]],x] /;
        FreeQ[{a,b,c,d,e,A,B,n},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (capital_a__ + capital_b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            / (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).sqrt(),
        with: [capital_a__, capital_b__, c__, d__, e__, n_, a__, b__, x_],
        optional: [capital_a__, capital_b__, c__, d__, e__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let logarithm = (&c__ * affine.pow(&n_)).log();
            let sqrt_base = (&a__ + &b__ * &logarithm).sqrt();
            let recursive_integrand = Atom::num(1) / &sqrt_base;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_coefficient =
                (Atom::num(2) * &capital_a__ * &b__ - &capital_b__ * (Atom::num(2) * &a__ + &b__ * &n_))
                    / (Atom::num(2) * &b__);

            rubi_simp(
                    &(&capital_b__ * &affine * &sqrt_base / (&b__ * &e__)),
                    x_,
                ) + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2770,
        source: "Int[x_^m_.*(d_+e_./x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[(e+d*x)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[m,q] && IntegerQ[q]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ / x_).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [m_, d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [m_, e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(m_, q_)
                && integerq!(q_)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = (&e__ + &d__ * x_).pow(&q_) * logarithmic.pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2800,
        source: "Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*Log[c_.*x_^n_.],x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^r)^q,x]},
          Log[c*x^n] \\[Star] u - n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{c,d,e,n,r},x] && IGtQ[q,0] && IntegerQ[m] && Not[EqQ[q,1] && EqQ[m,-1]]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(r_)).pow(q_) * (c__ * x_.pow(n_)).log(),
        with: [m_, d__, e__, r_, q_, c__, n_, x_],
        optional: [m_, e__, r_, q_, c__, n_],
        when: {
            freeq!([c__, d__, e__, n_, r_], x_)
                && igtq!(q_, 0)
                && integerq!(m_)
                && !(eqq!(q_, 1) && eqq!(m_, -1))
        },
        rhs: {
            let base_power = x_.pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base_power, x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u) - rubi_star(n_, recursive)
        },
    ));
}

fn push_rules_rule_2801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2801,
        source: "Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^r)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0] && IntegerQ[m] && Not[EqQ[q,1] && EqQ[m,-1]]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [m_, e__, r_, q_, b__, c__, n_],
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

            rubi_star(u, logarithmic) - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2773,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])/(d*f*(m+1)) -
          b*n/(d*(m+1)) \\[Star] Int[(f*x)^m*(d+e*x^r)^(q+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m+r*(q+1)+1,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, r_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && eqq!(&m_ + &r_ * (&q_ + 1) + 1, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &d__ * &f__ * (&m_ + 1);
            let recursive_denominator = &d__ * (&m_ + 1);
            let recursive_integrand = scaled.pow(&m_) * base.pow(&q_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled.pow(&m_ + 1) * base.pow(&q_ + 1) * logarithmic / denominator),
                    x_,
                ) - rubi_star(&b__ * &n_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2774,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_])^p_.,x_Symbol] :=
          f^m/n \\[Star] Subst[Int[(d+e*x)^q*(a+b*Log[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && EqQ[r,n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, e__, q_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && eqq!(m_, &r_ - 1)
                && igtq!(p_, 0)
                && (integerq!(m_) || gtq!(f__, 0))
                && eqq!(r_, n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&d__ + &e__ * &substitution_variable).pow(&q_)
                * (&a__ + &b__ * (&c__ * &substitution_variable).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(f__.pow(&m_), substituted / &n_)
        },
    ));
}

fn push_rules_rule_2775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2775,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_^r_),x_Symbol] :=
          f^m*Log[1+e*x^r/d]*(a+b*Log[c*x^n])^p/(e*r) -
          b*f^m*n*p/(e*r) \\[Star] Int[Log[1+e*x^r/d]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && NeQ[r,n]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / (d__ + e__ * x_.pow(r_)),
        with: [f__, m_, a__, b__, c__, n_, p_, d__, e__, r_, x_],
        optional: [f__, m_, a__, b__, c__, n_, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, r_], x_)
                && eqq!(m_, &r_ - 1)
                && igtq!(p_, 0)
                && (integerq!(m_) || gtq!(f__, 0))
                && neq!(r_, n_)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let substitution_log = (Atom::num(1) + &e__ * x_.pow(&r_) / &d__).log();
            let denominator = &e__ * &r_;
            let scaled_power = f__.pow(&m_);
            let recursive_integrand = &substitution_log * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&scaled_power * &substitution_log * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) - rubi_star(&b__ * scaled_power * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2776,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          f^m*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^p/(e*r*(q+1)) -
          b*f^m*n*p/(e*r*(q+1)) \\[Star] Int[(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && NeQ[r,n] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && eqq!(m_, &r_ - 1)
                && igtq!(p_, 0)
                && (integerq!(m_) || gtq!(f__, 0))
                && neq!(r_, n_)
                && neq!(q_, -1)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &e__ * &r_ * (&q_ + 1);
            let scaled_power = f__.pow(&m_);
            let recursive_integrand = base.pow(&q_ + 1) * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&scaled_power * base.pow(&q_ + 1) * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) - rubi_star(&b__ * scaled_power * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2777,
        source: "Int[(f_*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (f*x)^m/x^m \\[Star] Int[x^m*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && Not[(IntegerQ[m] || GtQ[f,0])]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [m_, e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && eqq!(m_, &r_ - 1)
                && igtq!(p_, 0)
                && !(integerq!(m_) || gtq!(f__, 0))
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = x_.pow(&m_) * base.pow(&q_) * logarithmic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled.pow(&m_), recursive / x_.pow(&m_))
        },
    ));
}

fn push_rules_rule_2784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2784,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          (f*x)^m*(d+e*x)^(q+1)*(a+b*Log[c*x^n])/(e*(q+1)) -
          f/(e*(q+1)) \\[Star] Int[(f*x)^(m-1)*(d+e*x)^(q+1)*(a*m+b*n+b*m*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && ILtQ[q,-1] && GtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * (d__ + e__ * x_).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [f__, m_, d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && iltq!(q_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_;
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let log_linear = &a__ + &b__ * &logarithmic;
            let denominator = &e__ * (&q_ + 1);
            let recursive_integrand = scaled.pow(&m_ - 1)
                * base.pow(&q_ + 1)
                * (&a__ * &m_ + &b__ * &n_ + &b__ * &m_ * logarithmic);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled.pow(&m_) * base.pow(&q_ + 1) * log_linear / &denominator),
                    x_,
                ) - rubi_star(f__, recursive / denominator)
        },
    ));
}

fn push_rules_rule_2785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2785,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*Log[c*x^n])/(2*d*f*(q+1)) +
          1/(2*d*(q+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^(q+1)*(a*(m+2*q+3)+b*n+b*(m+2*q+3)*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && ILtQ[q,-1] && ILtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [f__, m_, d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && iltq!(q_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let base = &d__ + &e__ * x_.pow(2);
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let log_linear = &a__ + &b__ * &logarithmic;
            let denominator = Atom::num(2) * &d__ * &f__ * (&q_ + 1);
            let recursive_denominator = Atom::num(2) * &d__ * (&q_ + 1);
            let coefficient = &m_ + Atom::num(2) * &q_ + 3;
            let recursive_integrand = scaled.pow(&m_)
                * base.pow(&q_ + 1)
                * (&a__ * &coefficient + &b__ * &n_ + &b__ * coefficient * logarithmic);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-scaled.pow(&m_ + 1) * base.pow(&q_ + 1) * log_linear / denominator),
                    x_,
                ) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2786,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          d^IntPart[q]*(d+e*x^2)^FracPart[q]/(1+e/d*x^2)^FracPart[q] \\[Star] Int[x^m*(1+e/d*x^2)^q*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m/2] && IntegerQ[q-1/2] && Not[LtQ[m+2*q,-2] || GtQ[d,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [m_, d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && integerq!(&m_ / 2)
                && integerq!(&q_ - Atom::num(1) / Atom::num(2))
                && !(ltq!(&m_ + Atom::num(2) * &q_, -2) || gtq!(d__, 0))
        },
        rhs: {
            let normalized_base = Atom::num(1) + &e__ * x_.pow(2) / &d__;
            let denominator = normalized_base.pow(rubi_frac_part(&q_));
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = x_.pow(&m_) * normalized_base.pow(&q_) * logarithmic;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(d__.pow(rubi_int_part(&q_)) * (&d__ + &e__ * x_.pow(2)).pow(rubi_frac_part(&q_)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, d2__, e1__, e2__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2787,
        source: "Int[x_^m_.*(d1_+e1_.*x_)^q_*(d2_+e2_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          (d1+e1*x)^q*(d2+e2*x)^q/(1+e1*e2/(d1*d2)*x^2)^q \\[Star] Int[x^m*(1+e1*e2/(d1*d2)*x^2)^q*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[d2*e1+d1*e2,0] && IntegerQ[m] && IntegerQ[q-1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_)
            * (d1__ + e1__ * x_).pow(q_)
            * (d2__ + e2__ * x_).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [m_, d1__, e1__, q_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
                && integerq!(m_)
                && integerq!(&q_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let normalized_base =
                Atom::num(1) + &e1__ * &e2__ * x_.pow(2) / (&d1__ * &d2__);
            let denominator = normalized_base.pow(&q_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = x_.pow(&m_) * normalized_base.pow(&q_) * logarithmic;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&d1__ + &e1__ * x_).pow(&q_) * (&d2__ + &e2__ * x_).pow(&q_) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, r_, x_);
    rules.push(rubi_rule!(
        order: 2778,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_])/(x_*(d_+e_.*x_^r_.)),x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*Log[c*x])/(x*(d+e*x^(r/n))),x],x,x^n] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IntegerQ[r/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()) / (x_ * (d__ + e__ * x_.pow(r_))),
        with: [a__, b__, c__, n_, d__, e__, r_, x_],
        optional: [a__, b__, c__, e__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && integerq!(&r_ / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * (&c__ * &substitution_variable).log())
                / (&substitution_variable * (&d__ + &e__ * substitution_variable.pow(&r_ / &n_)));
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2802,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
          1/d \\[Star] Int[(a+b*Log[c*x^n])^p/x,x] - e/d \\[Star] Int[(a+b*Log[c*x^n])^p/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / (x_ * (d__ + e__ * x_)),
        with: [a__, b__, c__, n_, p_, d__, e__, x_],
        optional: [a__, b__, c__, n_, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let recursive_integrand_1 = &logarithmic / x_;
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = logarithmic / (&d__ + &e__ * x_);
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_star(Atom::num(1) / &d__, recursive_1) - rubi_star(e__, recursive_2 / &d__)
        },
    ));
}

fn push_rules_rule_2779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2779,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(x_*(d_+e_.*x_^r_.)),x_Symbol] :=
          -Log[1+d/(e*x^r)]*(a+b*Log[c*x^n])^p/(d*r) +
          b*n*p/(d*r) \\[Star] Int[Log[1+d/(e*x^r)]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / (x_ * (d__ + e__ * x_.pow(r_))),
        with: [a__, b__, c__, n_, p_, d__, e__, r_, x_],
        optional: [a__, b__, c__, n_, p_, e__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let substitution_log = (Atom::num(1) + &d__ / (&e__ * x_.pow(&r_))).log();
            let denominator = &d__ * &r_;
            let recursive_integrand = &substitution_log * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&substitution_log * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) + rubi_star(&b__ * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2788,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          d \\[Star] Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^p/x,x] +
          e \\[Star] Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0] && GtQ[q,0] && IntegerQ[2*q]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 0)
                && gtq!(q_, 0)
                && integerq!(Atom::num(2) * &q_)
        },
        rhs: {
            let base = &d__ + &e__ * x_;
            let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let recursive_integrand_1 = base.pow(&q_ - 1) * &logarithmic / x_;
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = base.pow(&q_ - 1) * logarithmic;
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_star(d__, recursive_1)
                    + rubi_star(e__, recursive_2)
        },
    ));
}

fn push_rules_rule_2789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2789,
        source: "Int[(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          1/d \\[Star] Int[(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/x,x] -
          e/d \\[Star] Int[(d+e*x)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0] && LtQ[q,-1] && IntegerQ[2*q]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
                && integerq!(Atom::num(2) * &q_)
        },
        rhs: {
            let base = &d__ + &e__ * x_;
            let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let recursive_integrand_1 = base.pow(&q_ + 1) * &logarithmic / x_;
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = base.pow(&q_) * logarithmic;
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_star(Atom::num(1) / &d__, recursive_1)
                    - rubi_star(e__, recursive_2 / &d__)
        },
    ));
}

fn push_rules_rule_2790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2790,
        source: "Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])/x_,x_Symbol] :=
          With[{u=IntHide[(d+e*x^r)^q/x,x]},
          u*(a+b*Log[c*x^n]) - b*n \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IntegerQ[q-1/2]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()) / x_,
        with: [d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && integerq!(&q_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let hidden_integrand = (&d__ + &e__ * x_.pow(&r_)).pow(&q_) / x_;
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2791,
        source: "Int[(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          1/d \\[Star] Int[(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^p/x,x] -
          e/d \\[Star] Int[x^(r-1)*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[p,0] && ILtQ[q,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(r_)).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / x_,
        with: [d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let recursive_integrand_1 = base.pow(&q_ + 1) * &logarithmic / x_;
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = x_.pow(&r_ - 1) * base.pow(&q_) * logarithmic;
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_star(Atom::num(1) / &d__, recursive_1)
                    - rubi_star(e__, recursive_2 / &d__)
        },
    ));
}

fn push_rules_rule_2792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2792,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^r)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x] /;
         (EqQ[r,1] || EqQ[r,2]) && IntegerQ[m] && IntegerQ[q-1/2] || InverseFunctionFreeQ[u,x]] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && IntegerQ[2*q] && (IntegerQ[m] && IntegerQ[r] || IGtQ[q,0])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && integerq!(Atom::num(2) * &q_)
                && ((integerq!(m_) && integerq!(r_)) || igtq!(q_, 0))
                && rubi_int_hide_logarithm_condition(
                    &((&f__ * x_).pow(&m_)
                        * (&d__ + &e__ * x_.pow(&r_)).pow(&q_)),
                    x_,
                    (eqq!(r_, 1) || eqq!(r_, 2))
                        && integerq!(m_)
                        && integerq!(&q_ - Atom::num(1) / Atom::num(2)),
                )
        },
        rhs: {
            let hidden_integrand = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();

            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2793,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*x^n]),(f*x)^m*(d+e*x^r)^q,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IntegerQ[m] && IntegerQ[r])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_, r_], x_)
                && integerq!(q_)
                && (gtq!(q_, 0) || (integerq!(m_) && integerq!(r_)))
                && {
                    let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
                    let base_power = (&f__ * x_).pow(&m_)
                        * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
                    rubi_expand_integrand_product_sum(&logarithmic, &base_power, x_).is_some()
                }
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let base_power = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let u = rubi_expand_integrand_product_sum(&logarithmic, &base_power, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2794,
        source: "Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x^(r/n))^q*(a+b*Log[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p,q,r},x] && IntegerQ[q] && IntegerQ[r/n] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[p,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(r_)).pow(q_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [m_, e__, r_, q_, a__, b__, c__, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_, r_], x_)
                && integerq!(q_)
                && integerq!(&r_ / &n_)
                && integerq!(k)
                && (gtq!(k, 0) || igtq!(p_, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            let transformed_integrand = substitution_variable.pow(&k - 1)
                * (&d__ + &e__ * substitution_variable.pow(&r_ / &n_)).pow(&q_)
                * (&a__ + &b__ * (&c__ * &substitution_variable).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2795,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,(f*x)^m*(d+e*x^r)^q,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IGtQ[p,0] && IntegerQ[m] && IntegerQ[r])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, e__, r_, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
                && integerq!(q_)
                && (gtq!(q_, 0) || (igtq!(p_, 0) && integerq!(m_) && integerq!(r_)))
                && {
                    let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
                    let base_power = (&f__ * x_).pow(&m_)
                        * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
                    rubi_expand_integrand_product_sum(&logarithmic, &base_power, x_).is_some()
                }
        },
        rhs: {
            let logarithmic = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let base_power = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let u = rubi_expand_integrand_product_sum(&logarithmic, &base_power, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2796,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, e__, r_, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&r_)).pow(&q_)
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, m_, n_, p_, q_, u__, x_);
    let rule = rubi_rule!(
        order: 2797,
        source: "Int[(f_.*x_)^m_.*u_^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[(f*x)^m*ExpandToSum[u,x]^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,f,m,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (f__ * x_).pow(m_) * u__.pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [f__, m_, u__, q_, a__, b__, c__, n_, p_, x_],
        optional: [f__, m_, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, f__, m_, n_, p_, q_], x_)
                && rubi_binomial_q(&u__, x_)
                && !rubi_binomial_match_q(&u__, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * expanded_u.pow(&q_)
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__));
}

fn push_rules_rule_2803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, polyx__, x_);
    rules.push(rubi_rule!(
        order: 2803,
        source: "Int[Polyx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Polyx*(a+b*Log[c*x^n])^p,x],x] /;
        FreeQ[{a,b,c,n,p},x] && PolynomialQ[Polyx,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: polyx__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [polyx__, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && rubi_polynomial_q(&polyx__, x_)
        },
        rhs: {
            let expand_integrand_payload =
                &polyx__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 2804,
        source: "Int[RFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,n},x] && RationalFunctionQ[RFx,x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [rfx__, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(p_, 0)
                && {
                    let log_power = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
                    rubi_expand_integrand_product_sum(&log_power, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let log_power = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let u = rubi_expand_integrand_product_sum(&log_power, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 2805,
        source: "Int[RFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[RFx*(a+b*Log[c*x^n])^p,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,n},x] && RationalFunctionQ[RFx,x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [rfx__, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(p_, 0)
                && {
                    rubi_expand_integrand_sum(
                        &(&rfx__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_)),
                        x_,
                    )
                    .is_some()
                }
        },
        rhs: {
            let u = rubi_expand_integrand_sum(
                &(&rfx__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_)),
                x_,
            )
            .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(afx__, a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2806,
        source: "Int[AFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[AFx*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x] && AlgebraicFunctionQ[AFx,x,True]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: afx__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [afx__, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && rubi_algebraic_function_q(&afx__, x_, true)
        },
        rhs: {
            let integrand =
                &afx__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2807,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_+e_.*Log[c_.*x_^n_.])^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[c*x^n])^p*(d+e*Log[c*x^n])^q,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            * (d__ + e__ * (c__ * x_.pow(n_)).log()).pow(q_),
        with: [a__, b__, c__, n_, p_, d__, e__, q_, x_],
        optional: [a__, b__, c__, n_, p_, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && integerq!(p_)
                && integerq!(q_)
        },
        rhs: {
            let logarithm = (&c__ * x_.pow(&n_)).log();
            let expand_integrand_payload =
                (&a__ + &b__ * &logarithm).pow(&p_) * (&d__ + &e__ * logarithm).pow(&q_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2808,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.]),x_Symbol] :=
          With[{u=IntHide[(a+b*Log[c*x^n])^p,x]},
          (d+e*Log[f*x^r]) \\[Star] u - e*r \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,n,p,r},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            * (d__ + e__ * (f__ * x_.pow(r_)).log()),
        with: [a__, b__, c__, n_, p_, d__, e__, f__, r_, x_],
        optional: [a__, b__, c__, n_, p_, d__, e__, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, r_], x_)
        },
        rhs: {
            let hidden_integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let multiplier = &d__ + &e__ * (&f__ * x_.pow(&r_)).log();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, u) - rubi_star(&e__ * &r_, recursive)
        },
    ));
}

fn push_rules_rule_2809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2809,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
          x*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q -
          e*q*r \\[Star] Int[(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^(q-1),x] -
          b*n*p \\[Star] Int[(a+b*Log[c*x^n])^(p-1)*(d+e*Log[f*x^r])^q,x] /;
        FreeQ[{a,b,c,d,e,f,n,r},x] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, d__, e__, f__, r_, q_, x_],
        optional: [a__, b__, c__, n_, p_, d__, e__, f__, r_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, r_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let first_log = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let second_log = &d__ + &e__ * (&f__ * x_.pow(&r_)).log();
            let recursive_integrand_1 = first_log.pow(&p_) * second_log.pow(&q_ - 1);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = first_log.pow(&p_ - 1) * second_log.pow(&q_);
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(&(x_ * first_log.pow(&p_) * second_log.pow(&q_)), x_)
                    - rubi_star(&e__ * &q_ * &r_, recursive_1)
                    - rubi_star(&b__ * &n_ * &p_, recursive_2)
        },
    ));
}

fn push_rules_rule_2810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2810,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
          Unintegrable[(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q,x] /;
        FreeQ[{a,b,c,d,e,f,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, d__, e__, f__, r_, q_, x_],
        optional: [a__, b__, c__, n_, p_, d__, e__, f__, r_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_)
                * (&d__ + &e__ * (&f__ * x_.pow(&r_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, v_);
    rules.push(rubi_rule!(
        order: 2811,
        source: "Int[(a_.+b_.*Log[v_])^p_.*(c_.+d_.*Log[v_])^q_.,x_Symbol] :=
          1/Coeff[v,x,1] \\[Star] Subst[Int[(a+b*Log[x])^p*(c+d*Log[x])^q,x],x,v] /;
        FreeQ[{a,b,c,d,p,q},x] && LinearQ[v,x] && NeQ[Coeff[v,x,0],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * Atom::var(v_).log()).pow(p_)
            * (c__ + d__ * Atom::var(v_).log()).pow(q_),
        with: [a__, b__, v_, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && rubi_linear_q(&v_, x_)
                && rubi_coeff(&v_, x_, 0).is_some_and(|v0| neq!(v0, 0))
        },
        rhs: {
            let v1 = rubi_coeff(&v_, x_, 1).expect("LinearQ should provide Coeff[v,x,1]");
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * substitution_variable.log()).pow(&p_)
                * (&c__ + &d__ * substitution_variable.log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, &v_);

            rubi_star(Atom::num(1) / v1, substituted)
        },
    ));
}

fn push_rules_rule_2812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2812,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[c_.*x_^n_.])^q_./x_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*x)^p*(d+e*x)^q,x],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,e,n,p,q},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            * (d__ + e__ * (c__ * x_.pow(n_)).log()).pow(q_)
            / x_,
        with: [a__, b__, c__, n_, p_, d__, e__, q_, x_],
        optional: [a__, b__, c__, n_, p_, d__, e__, q_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * &substitution_variable).pow(&p_)
                * (&d__ + &e__ * substitution_variable).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&c__ * x_.pow(&n_)).log();
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2813,
        source: "Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.]),x_Symbol] :=
          With[{u=IntHide[(g*x)^m*(a+b*Log[c*x^n])^p,x]},
          (d+e*Log[f*x^r]) \\[Star] u - e*r \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,r},x] && Not[EqQ[p,1] && EqQ[a,0] && NeQ[d,0]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            * (d__ + e__ * (f__ * x_.pow(r_)).log()),
        with: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_, x_],
        optional: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, r_], x_)
                && !(eqq!(p_, 1) && eqq!(a__, 0) && neq!(d__, 0))
        },
        rhs: {
            let first_log = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let hidden_integrand = (&g__ * x_).pow(&m_) * first_log.pow(&p_);
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let multiplier = &d__ + &e__ * (&f__ * x_.pow(&r_)).log();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, u)
                    - rubi_star(&e__ * &r_, recursive)
        },
    ));
}

fn push_rules_rule_2814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2814,
        source: "Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
          (g*x)^(m+1)*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q/(g*(m+1)) -
          e*q*r/(m+1) \\[Star] Int[(g*x)^m*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^(q-1),x] -
          b*n*p/(m+1) \\[Star] Int[(g*x)^m*(a+b*Log[c*x^n])^(p-1)*(d+e*Log[f*x^r])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,r},x] && IGtQ[p,0] && IGtQ[q,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_, q_, x_],
        optional: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, r_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &g__ * x_;
            let first_log = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let second_log = &d__ + &e__ * (&f__ * x_.pow(&r_)).log();
            let m_plus_one = &m_ + 1;
            let recursive_integrand_1 =
                scaled.pow(&m_) * first_log.pow(&p_) * second_log.pow(&q_ - 1);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 =
                scaled.pow(&m_) * first_log.pow(&p_ - 1) * second_log.pow(&q_);
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(
                    &(scaled.pow(&m_ + 1) * first_log.pow(&p_) * second_log.pow(&q_)
                        / (&g__ * &m_plus_one)),
                    x_,
                ) - rubi_star(&e__ * &q_ * &r_ / &m_plus_one, recursive_1)
                    - rubi_star(&b__ * &n_ * &p_ / m_plus_one, recursive_2)
        },
    ));
}

fn push_rules_rule_2815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2815,
        source: "Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
          Unintegrable[(g*x)^m*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_, q_, x_],
        optional: [g__, m_, a__, b__, c__, n_, p_, d__, e__, f__, r_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_)
                * (&d__ + &e__ * (&f__ * x_.pow(&r_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, q_, u__, v_);
    rules.push(rubi_rule!(
        order: 2816,
        source: "Int[u_^m_.*(a_.+b_.*Log[v_])^p_.*(c_.+d_.*Log[v_])^q_.,x_Symbol] :=
          With[{e=Coeff[u,x,0],f=Coeff[u,x,1],g=Coeff[v,x,0],h=Coeff[v,x,1]},
          1/h \\[Star] Subst[Int[(f*x/h)^m*(a+b*Log[x])^p*(c+d*Log[x])^q,x],x,v] /;
         EqQ[f*g-e*h,0] && NeQ[g,0]] /;
        FreeQ[{a,b,c,d,m,p,q},x] && LinearQ[{u,v},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__.pow(m_)
            * (a__ + b__ * Atom::var(v_).log()).pow(p_)
            * (c__ + d__ * Atom::var(v_).log()).pow(q_),
        with: [u__, m_, a__, b__, v_, p_, c__, d__, q_, x_],
        optional: [m_, a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_, q_], x_)
                && rubi_linear_q_list(&[&u__, &v_], x_)
                && {
                    let e = rubi_coeff(&u__, x_, 0).expect("LinearQ should provide Coeff[u,x,0]");
                    let f = rubi_coeff(&u__, x_, 1).expect("LinearQ should provide Coeff[u,x,1]");
                    let g = rubi_coeff(&v_, x_, 0).expect("LinearQ should provide Coeff[v,x,0]");
                    let h = rubi_coeff(&v_, x_, 1).expect("LinearQ should provide Coeff[v,x,1]");
                    eqq!(&f * &g - &e * &h, 0) && neq!(g, 0)
                }
        },
        rhs: {
            let f = rubi_coeff(&u__, x_, 1).expect("LinearQ should provide Coeff[u,x,1]");
            let h = rubi_coeff(&v_, x_, 1).expect("LinearQ should provide Coeff[v,x,1]");
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&f * &substitution_variable / &h).pow(&m_)
                * (&a__ + &b__ * substitution_variable.log()).pow(&p_)
                * (&c__ + &d__ * substitution_variable.log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, &v_);

            rubi_star(Atom::num(1) / h, substituted)
        },
    ));
}

fn push_rules_rule_2817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2817,
        source: "Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=IntHide[Log[d*(e+f*x^m)^r],x]},
          (a+b*Log[c*x^n])^p \\[Star] u - b*n*p \\[Star] Int[(a+b*Log[c*x^n])^(p-1)/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && RationalQ[m] && (EqQ[p,1] || FractionQ[m] && IntegerQ[1/m] || EqQ[r,1] && EqQ[m,1] && EqQ[d*e,1])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, r_, m_, n_], x_)
                && igtq!(p_, 0)
                && rationalq!(m_)
                && (eqq!(p_, 1)
                    || (fractionq!(m_) && integerq!(Atom::num(1) / &m_))
                    || (eqq!(r_, 1) && eqq!(m_, 1) && eqq!(&d__ * &e__, 1)))
        },
        rhs: {
            let hidden_integrand = (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log();
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand =
                rubi_star(logarithmic.pow(&p_ - 1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic.pow(&p_), u)
                    - rubi_star(&b__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2818,
        source: "Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=IntHide[(a+b*Log[c*x^n])^p,x]},
          Log[d*(e+f*x^m)^r] \\[Star] u - f*m*r \\[Star] Int[x^(m-1)/(e+f*x^m) \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, r_, m_, n_], x_)
                && igtq!(p_, 0)
                && integerq!(m_)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&logarithmic.pow(&p_), x_).rubi_rhs();
            let multiplier = (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log();
            let recursive_integrand = rubi_star(
                x_.pow(&m_ - 1) / (&e__ + &f__ * x_.pow(&m_)),
                &u,
            );
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, u)
                    - rubi_star(&f__ * &m_ * &r_, recursive)
        },
    ));
}

fn push_rules_rule_2819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2819,
        source: "Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,r,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, r_, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log()
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, r_, u__, x_);
    let rule = rubi_rule!(
        order: 2820,
        source: "Int[Log[d_.*u_^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[Log[d*ExpandToSum[u,x]^r]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,r,n,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (d__ * u__.pow(r_)).log() * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [d__, u__, r_, a__, b__, c__, n_, p_, x_],
        optional: [d__, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, r_, n_, p_], x_)
                && rubi_binomial_q(&u__, x_)
                && !rubi_binomial_match_q(&u__, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let recursive_integrand = (&d__ * expanded_u.pow(&r_)).log()
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__));
}

fn push_rules_rule_2821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2821,
        source: "Int[Log[d_.*(e_+f_.*x_^m_.)]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          -PolyLog[2,-d*f*x^m]*(a+b*Log[c*x^n])^p/m +
          b*n*p/m \\[Star] Int[PolyLog[2,-d*f*x^m]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0] && EqQ[d*e,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * (e__ + f__ * x_.pow(m_))).log()
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / x_,
        with: [d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, f__, m_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && igtq!(p_, 0)
                && eqq!(&d__ * &e__, 1)
        },
        rhs: {
            let polylog = (-&d__ * &f__ * x_.pow(&m_)).polylog(2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = &polylog * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&polylog * logarithmic.pow(&p_) / &m_), x_)
                    + rubi_star(&b__ * &n_ * &p_ / &m_, recursive)
        },
    ));
}

fn push_rules_rule_2822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, r_, x_);
    rules.push(rubi_rule!(
        order: 2822,
        source: "Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) -
          f*m*r/(b*n*(p+1)) \\[Star] Int[x^(m-1)*(a+b*Log[c*x^n])^(p+1)/(e+f*x^m),x] /;
        FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && NeQ[d*e,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * (e__ + f__ * x_.pow(m_)).pow(r_)).log()
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
            / x_,
        with: [d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, r_, m_, n_], x_)
                && igtq!(p_, 0)
                && neq!(&d__ * &e__, 1)
        },
        rhs: {
            let p1 = &p_ + 1;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let multiplier = (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log();
            let denominator = &b__ * &n_ * &p1;
            let recursive_integrand =
                x_.pow(&m_ - 1) * logarithmic.pow(&p1) / (&e__ + &f__ * x_.pow(&m_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(multiplier * logarithmic.pow(&p1) / &denominator), x_)
                    - rubi_star(&f__ * &m_ * &r_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2823,
        source: "Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[(g*x)^q*Log[d*(e+f*x^m)^r],x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g,r,m,n,q},x] && (IntegerQ[(q+1)/m] || RationalQ[m] && RationalQ[q]) && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ * x_).pow(q_)
            * (d__ * (e__ + f__ * x_.pow(m_)).pow(r_)).log()
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [g__, q_, d__, e__, f__, m_, r_, a__, b__, c__, n_, x_],
        optional: [g__, q_, d__, f__, m_, r_, a__, b__, c__, n_],
        when: {
            let integer_ratio = integerq!((&q_ + 1) / &m_);
            freeq!([a__, b__, c__, d__, e__, f__, g__, r_, m_, n_, q_], x_)
                && (integer_ratio || (rationalq!(m_) && rationalq!(q_)))
                && neq!(q_, -1)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let hidden_integrand = (&g__ * x_).pow(&q_)
                * (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log();
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2824,
        source: "Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=IntHide[(g*x)^q*Log[d*(e+f*x^m)],x]},
          (a+b*Log[c*x^n])^p \\[Star] u - b*n*p \\[Star] Int[(a+b*Log[c*x^n])^(p-1)/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && IGtQ[p,0] && RationalQ[m] && RationalQ[q] && NeQ[q,-1] &&
          (EqQ[p,1] || FractionQ[m] && IntegerQ[(q+1)/m] || IGtQ[q,0] && IntegerQ[(q+1)/m] && EqQ[d*e,1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ * x_).pow(q_)
            * (d__ * (e__ + f__ * x_.pow(m_))).log()
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [g__, q_, d__, e__, f__, m_, a__, b__, c__, n_, p_, x_],
        optional: [g__, q_, d__, f__, m_, a__, b__, c__, n_, p_],
        when: {
            let integer_ratio = integerq!((&q_ + 1) / &m_);
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_], x_)
                && igtq!(p_, 0)
                && rationalq!(m_)
                && rationalq!(q_)
                && neq!(q_, -1)
                && (eqq!(p_, 1)
                    || (fractionq!(m_) && integer_ratio)
                    || (igtq!(q_, 0) && integer_ratio && eqq!(&d__ * &e__, 1)))
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let hidden_integrand =
                (&g__ * x_).pow(&q_) * (&d__ * (&e__ + &f__ * x_.pow(&m_))).log();
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let recursive_integrand =
                rubi_star(logarithmic.pow(&p_ - 1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic.pow(&p_), u)
                    - rubi_star(&b__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2825,
        source: "Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=IntHide[(g*x)^q*(a+b*Log[c*x^n])^p,x]},
          Log[d*(e+f*x^m)^r] \\[Star] u - f*m*r \\[Star] Int[x^(m-1)/(e+f*x^m) \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g,r,m,n,q},x] && IGtQ[p,0] && RationalQ[m] && RationalQ[q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, q_, d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [g__, q_, d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, r_, m_, n_, q_], x_)
                && igtq!(p_, 0)
                && rationalq!(m_)
                && rationalq!(q_)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&((&g__ * x_).pow(&q_) * logarithmic.pow(&p_)), x_).rubi_rhs();
            let multiplier = (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log();
            let recursive_integrand = rubi_star(
                x_.pow(&m_ - 1) / (&e__ + &f__ * x_.pow(&m_)),
                &u,
            );
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, u)
                    - rubi_star(&f__ * &m_ * &r_, recursive)
        },
    ));
}

fn push_rules_rule_2826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2826,
        source: "Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(g*x)^q*Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,r,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, q_, d__, e__, f__, m_, r_, a__, b__, c__, n_, p_, x_],
        optional: [g__, q_, d__, f__, m_, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, r_, m_, n_, p_, q_], x_)
        },
        rhs: {
            let integrand = (&g__ * x_).pow(&q_)
                * (&d__ * (&e__ + &f__ * x_.pow(&m_)).pow(&r_)).log()
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, n_, p_, q_, r_, u__, x_);
    let rule = rubi_rule!(
        order: 2827,
        source: "Int[(g_.*x_)^q_.*Log[d_.*u_^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[(g*x)^q*Log[d*ExpandToSum[u,x]^r]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,g,r,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (g__ * x_).pow(q_) * (d__ * u__.pow(r_)).log()
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [g__, q_, d__, u__, r_, a__, b__, c__, n_, p_, x_],
        optional: [g__, q_, d__, r_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, g__, r_, n_, p_, q_], x_)
                && rubi_binomial_q(&u__, x_)
                && !rubi_binomial_match_q(&u__, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let recursive_integrand = (&g__ * x_).pow(&q_)
                * (&d__ * expanded_u.pow(&r_)).log()
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__));
}

fn push_rules_rule_2828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, k_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2828,
        source: "Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          -b*n*x*PolyLog[k,e*x^q] + x*PolyLog[k,e*x^q]*(a+b*Log[c*x^n]) +
          b*n*q \\[Star] Int[PolyLog[k-1,e*x^q],x] - q \\[Star] Int[PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,e,n,q},x] && IGtQ[k,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_.pow(q_)).polylog(k_) * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [k_, e__, q_, a__, b__, c__, n_, x_],
        optional: [e__, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, e__, n_, q_], x_) && igtq!(k_, 0)
        },
        rhs: {
            let polylog = (&e__ * x_.pow(&q_)).polylog(&k_);
            let lowered_polylog = (&e__ * x_.pow(&q_)).polylog(&k_ - 1);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_1 = rubi_rhs_int(&lowered_polylog, x_);
            let recursive_2 = rubi_rhs_int(&(&lowered_polylog * &logarithmic), x_);

            rubi_simp(&(-&b__ * &n_ * x_ * &polylog), x_)
                    + rubi_simp(&(x_ * &polylog * logarithmic), x_)
                    + rubi_star(&b__ * &n_ * &q_, recursive_1)
                    - rubi_star(q_, recursive_2)
        },
    ));
}

fn push_rules_rule_2829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, k_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2829,
        source: "Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,e,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_.pow(q_)).polylog(k_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [k_, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, e__, n_, p_, q_], x_)
        },
        rhs: {
            let integrand = (&e__ * x_.pow(&q_)).polylog(&k_)
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, k_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2830,
        source: "Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          PolyLog[k+1,e*x^q]*(a+b*Log[c*x^n])^p/q - b*n*p/q \\[Star] Int[PolyLog[k+1,e*x^q]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,e,k,n,q},x] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [k_, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, e__, k_, n_, q_], x_) && gtq!(p_, 0)
        },
        rhs: {
            let raised_polylog = (&e__ * x_.pow(&q_)).polylog(&k_ + 1);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = &raised_polylog * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(raised_polylog * logarithmic.pow(&p_) / &q_), x_)
                    - rubi_star(&b__ * &n_ * &p_ / &q_, recursive)
        },
    ));
}

fn push_rules_rule_2831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, k_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2831,
        source: "Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) - q/(b*n*(p+1)) \\[Star] Int[PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n])^(p+1)/x,x] /;
        FreeQ[{a,b,c,e,k,n,q},x] && LtQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [k_, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, e__, k_, n_, q_], x_) && ltq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + 1;
            let polylog = (&e__ * x_.pow(&q_)).polylog(&k_);
            let lowered_polylog = (&e__ * x_.pow(&q_)).polylog(&k_ - 1);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &b__ * &n_ * &p1;
            let recursive_integrand = lowered_polylog * logarithmic.pow(&p1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_coefficient = &q_ / &denominator;

            rubi_simp(&(polylog * logarithmic.pow(&p1) / &denominator), x_)
                    - rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, k_, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2832,
        source: "Int[(d_.*x_)^m_.*PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          -b*n*(d*x)^(m+1)*PolyLog[k,e*x^q]/(d*(m+1)^2) +
          (d*x)^(m+1)*PolyLog[k,e*x^q]*(a+b*Log[c*x^n])/(d*(m+1)) +
          b*n*q/(m+1)^2 \\[Star] Int[(d*x)^m*PolyLog[k-1,e*x^q],x] -
          q/(m+1) \\[Star] Int[(d*x)^m*PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,m,n,q},x] && IGtQ[k,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (e__ * x_.pow(q_)).polylog(k_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [d__, m_, k_, e__, q_, a__, b__, c__, n_, x_],
        optional: [d__, m_, e__, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_], x_)
                && igtq!(k_, 0)
        },
        rhs: {
            let m1 = &m_ + 1;
            let scaled = &d__ * x_;
            let polylog = (&e__ * x_.pow(&q_)).polylog(&k_);
            let lowered_polylog = (&e__ * x_.pow(&q_)).polylog(&k_ - 1);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let scaled_power_m = scaled.pow(&m_);
            let scaled_power_m1 = scaled.pow(&m1);
            let m1_squared = m1.pow(2);
            let recursive_1 = rubi_rhs_int(&(&scaled_power_m * &lowered_polylog), x_);
            let recursive_2 =
                rubi_rhs_int(&(scaled_power_m * &lowered_polylog * &logarithmic), x_);

            rubi_simp(
                    &(-&b__ * &n_ * &scaled_power_m1 * &polylog / (&d__ * &m1_squared)),
                    x_,
                ) + rubi_simp(
                    &(&scaled_power_m1 * &polylog * logarithmic / (&d__ * &m1)),
                    x_,
                ) - rubi_star(&q_, recursive_2 / &m1)
                    + rubi_star(&b__ * &n_ * &q_ / &m1_squared, recursive_1)
        },
    ));
}

fn push_rules_rule_2833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, k_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2833,
        source: "Int[(d_.*x_)^m_.*PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d*x)^m*PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (d__ * x_).pow(m_)
            * (e__ * x_.pow(q_)).polylog(k_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [d__, m_, k_, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
        },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * (&e__ * x_.pow(&q_)).polylog(&k_)
                * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2834,
        source: "Int[Px_.*F_[d_.*(e_.+f_.*x_)]^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[Px*F[d*(e+f*x)]^m,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && PolynomialQ[Px,x] && IGtQ[m,0] && MemberQ[{ArcSin, ArcCos, ArcSinh, ArcCosh},F]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * capital_f_.call(d__ * (e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [px__, capital_f_, d__, e__, f__, m_, a__, b__, c__, n_, x_],
        optional: [px__, d__, e__, f__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && igtq!(m_, 0)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbol!("asin"),
                        symbol!("acos"),
                        symbol!("asinh"),
                        symbol!("acosh"),
                    ],
                )
        },
        rhs: {
            let inverse =
                rubi_function_head_symbol(&capital_f_).rubi_rhs().call(&d__ * (&e__ + &f__ * x_));
            let hidden_integrand = &px__ * inverse.pow(&m_);
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2835,
        source: "Int[Px_.*F_[d_.*(e_.+f_.*x_)]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[Px*F[d*(e+f*x)],x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,n},x] && PolynomialQ[Px,x] && MemberQ[{ArcTan, ArcCot, ArcTanh, ArcCoth},F]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * capital_f_.call(d__ * (e__ + f__ * x_))
            * (a__ + b__ * (c__ * x_.pow(n_)).log()),
        with: [px__, capital_f_, d__, e__, f__, a__, b__, c__, n_, x_],
        optional: [px__, d__, e__, f__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbol!("atan"),
                        symbol!("acot"),
                        symbol!("atanh"),
                        symbol!("acoth"),
                    ],
                )
        },
        rhs: {
            let inverse =
                rubi_function_head_symbol(&capital_f_).rubi_rhs().call(&d__ * (&e__ + &f__ * x_));
            let hidden_integrand = &px__ * inverse;
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) * (d__ + e__ * (f__ * x_.pow(r_)).log()).pow(q_)
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
    let p_ = symbols.p_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ * (e__ + f__ * x_.pow(m_)).pow(r_)).log() * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / x_
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let e__ = symbols.e__;
    let k_ = symbols.k_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_.pow(q_)).polylog(k_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / x_
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
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log())
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
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(r_)).pow(q_)
        * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
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
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
        * (d__ + e__ * (f__ * x_.pow(r_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
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
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(q_)
        * (d__ * (e__ + f__ * x_.pow(m_)).pow(r_)).log()
        * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let rfx__ = symbols.rfx__;
    let x_ = symbols.x_;
    rfx__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}
