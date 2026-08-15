use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2750(rules);
    push_rules_rule_2751(rules);
    push_rules_rule_2752(rules);
    push_rules_rule_2753(rules);
    push_rules_rule_2754(rules);
    push_rules_rule_2755(rules);
    push_rules_rule_2756(rules);
    push_rules_rule_2757(rules);
    push_rules_rule_2758(rules);
    push_rules_rule_2759(rules);
    push_rules_rule_2760(rules);
    push_rules_rule_2761(rules);
    push_rules_rule_2762(rules);
    push_rules_rule_2763(rules);
    push_rules_rule_2764(rules);
    push_rules_rule_2765(rules);
    push_rules_rule_2766(rules);
    push_rules_rule_2767(rules);
    push_rules_rule_2768(rules);
    push_rules_rule_2769(rules);
}

fn push_rules_rule_2750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2750,
        source: "Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^r)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x]] /;
        FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, r_], x_)
                && igtq!(q_, 0)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base.pow(&q_), x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2751,
        source: "Int[(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          x*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])/d - b*n/d \\[Star] Int[(d+e*x^r)^(q+1),x] /;
        FreeQ[{a,b,c,d,e,n,q,r},x] && EqQ[r*(q+1)+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [e__, r_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_, r_], x_)
                && eqq!(&r_ * (&q_ + 1) + 1, 0)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = base.pow(&q_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * base.pow(&q_ + 1) * logarithmic / &d__), x_)
                    - rubi_star(&b__ * &n_ / &d__, recursive)
        },
    ));
}

fn push_rules_rule_2752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2752,
        source: "Int[Log[c_.*x_]/(d_+e_.*x_),x_Symbol] :=
          -1/e*PolyLog[2,1-c*x] /;
        FreeQ[{c,d,e},x] && EqQ[e+c*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ * x_).log() / (d__ + e__ * x_),
        with: [c__, d__, e__, x_],
        optional: [c__, e__],
        when: {
            freeq!([c__, d__, e__], x_)
                && eqq!(&e__ + &c__ * &d__, 0)
        },
        rhs: {
            let argument = Atom::num(1) - &c__ * x_;

            rubi_simp(&(-argument.polylog(2) / &e__), x_)
        },
    ));
}

fn push_rules_rule_2753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2753,
        source: "Int[(a_.+b_.*Log[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
          (a+b*Log[-c*d/e])*Log[d+e*x]/e + b \\[Star] Int[Log[-e*x/d]/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[-c*d/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).log()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(-&c__ * &d__ / &e__, 0)
        },
        rhs: {
            let first =
                (&a__ + &b__ * (-&c__ * &d__ / &e__).log()) * (&d__ + &e__ * x_).log()
                    / &e__;
            let recursive_integrand = (-&e__ * x_ / &d__).log() / (&d__ + &e__ * x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&first, x_) + rubi_star(b__, recursive)
        },
    ));
}

fn push_rules_rule_2754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2754,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_),x_Symbol] :=
          Log[1+e*x/d]*(a+b*Log[c*x^n])^p/e - b*n*p/e \\[Star] Int[Log[1+e*x/d]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, n_, p_, d__, e__, x_],
        optional: [a__, b__, c__, n_, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let log_affine = (Atom::num(1) + &e__ * x_ / &d__).log();
            let recursive_integrand = &log_affine * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(log_affine * logarithmic.pow(&p_) / &e__), x_)
                    - rubi_star(&b__ * &n_ * &p_ / &e__, recursive)
        },
    ));
}

fn push_rules_rule_2755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2755,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_)^2,x_Symbol] :=
          x*(a+b*Log[c*x^n])^p/(d*(d+e*x)) - b*n*p/d \\[Star] Int[(a+b*Log[c*x^n])^(p-1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / (d__ + e__ * x_).pow(2),
        with: [a__, b__, c__, n_, p_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && gtq!(p_, 0)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = logarithmic.pow(&p_ - 1) / &affine;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic.pow(&p_) / (&d__ * affine)), x_)
                    - rubi_star(&b__ * &n_ * &p_ / &d__, recursive)
        },
    ));
}

fn push_rules_rule_2756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2756,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/(e*(q+1)) - b*n*p/(e*(q+1)) \\[Star] Int[((d+e*x)^(q+1)*(a+b*Log[c*x^n])^(p-1))/x,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && GtQ[p,0] && NeQ[q,-1] && (EqQ[p,1] || IntegersQ[2*p,2*q] && Not[IGtQ[q,0]] || EqQ[p,2] && NeQ[q,1])",
        desc: "Integration by parts",
        refs: ["G&R 2.728.1, CRC 501, A&S 4.1.50'"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && gtq!(p_, 0)
                && neq!(q_, -1)
                && (eqq!(p_, 1)
                    || (integersq!([Atom::num(2) * &p_, Atom::num(2) * &q_])
                        && !igtq!(q_, 0))
                    || (eqq!(p_, 2) && neq!(q_, 1)))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let denominator = &e__ * (&q_ + 1);
            let recursive_integrand =
                affine.pow(&q_ + 1) * logarithmic.pow(&p_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&q_ + 1) * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) - rubi_star(&b__ * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2757,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          x*(d+e*x)^q*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) +
          d*q/(b*n*(p+1)) \\[Star] Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^(p+1),x] -
          (q+1)/(b*n*(p+1)) \\[Star] Int[(d+e*x)^q*(a+b*Log[c*x^n])^(p+1),x] /;
        FreeQ[{a,b,c,d,e,n},x] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let denominator = &b__ * &n_ * (&p_ + 1);
            let affine = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let raised_power = &p_ + 1;
            let recursive_integrand_1 = affine.pow(&q_ - 1) * logarithmic.pow(&raised_power);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = affine.pow(&q_) * logarithmic.pow(&raised_power);
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(
                    &(x_ * affine.pow(&q_) * logarithmic.pow(&raised_power) / &denominator),
                    x_,
                ) + rubi_star(&d__ * &q_ / &denominator, recursive_1)
                    - rubi_star(&q_ + 1, recursive_2 / denominator)
        },
    ));
}

fn push_rules_rule_2758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2758,
        source: "Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          x*(d+e*x^2)^q*(a+b*Log[c*x^n])/(2*q+1) -
          b*n/(2*q+1) \\[Star] Int[(d+e*x^2)^q,x] +
          2*d*q/(2*q+1) \\[Star] Int[(d+e*x^2)^(q-1)*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,n},x] && GtQ[q,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [e__, q_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && gtq!(q_, 0) },
        rhs: {
            let denominator = Atom::num(2) * &q_ + 1;
            let base = &d__ + &e__ * x_.pow(2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand_1 = base.pow(&q_);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = base.pow(&q_ - 1) * &logarithmic;
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(
                    &(x_ * base.pow(&q_) * logarithmic / &denominator),
                    x_,
                ) - rubi_star(&b__ * &n_ / &denominator, recursive_1)
                    + rubi_star(Atom::num(2) * &d__ * &q_ / denominator, recursive_2)
        },
    ));
}

fn push_rules_rule_2759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2759,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
          x*(a+b*Log[c*x^n])/(d*Sqrt[d+e*x^2]) - b*n/d \\[Star] Int[1/Sqrt[d+e*x^2],x] /;
        FreeQ[{a,b,c,d,e,n},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log())
            / (d__ + e__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) },
        rhs: {
            let base = &d__ + &e__ * x_.pow(2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = Atom::num(1) / base.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic / (&d__ * base.sqrt())), x_)
                    - rubi_star(&b__ * &n_ / &d__, recursive)
        },
    ));
}

fn push_rules_rule_2760(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2760,
        source: "Int[(d_+e_.*x_^2)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          -x*(d+e*x^2)^(q+1)*(a+b*Log[c*x^n])/(2*d*(q+1)) +
          b*n/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1),x] +
          (2*q+3)/(2*d*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,n},x] && LtQ[q,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && ltq!(q_, -1) },
        rhs: {
            let denominator = Atom::num(2) * &d__ * (&q_ + 1);
            let base = &d__ + &e__ * x_.pow(2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let raised_power = &q_ + 1;
            let recursive_integrand_1 = base.pow(&raised_power);
            let recursive_1 = rubi_rhs_int(&recursive_integrand_1, x_);
            let recursive_integrand_2 = base.pow(&raised_power) * &logarithmic;
            let recursive_2 = rubi_rhs_int(&recursive_integrand_2, x_);

            rubi_simp(
                    &(Atom::num(-1) * x_ * base.pow(&raised_power) * logarithmic / &denominator),
                    x_,
                ) + rubi_star(&b__ * &n_ / &denominator, recursive_1)
                    + rubi_star(Atom::num(2) * &q_ + 3, recursive_2 / denominator)
        },
    ));
}

fn push_rules_rule_2761(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2761,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2),x_Symbol] :=
          With[{u=IntHide[1/(d+e*x^2),x]},
          u*(a+b*Log[c*x^n]) - b*n \\[Star] Int[u/x,x]] /;
        FreeQ[{a,b,c,d,e,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&(Atom::num(1) / (&d__ + &e__ * x_.pow(2))), x_).rubi_rhs();
            let recursive_integrand = &u / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2762,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          ArcSinh[Rt[e,2]*x/Sqrt[d]]*(a+b*Log[c*x^n])/Rt[e,2] - b*n/Rt[e,2] \\[Star] Int[ArcSinh[Rt[e,2]*x/Sqrt[d]]/x,x] /;
        FreeQ[{a,b,c,d,e,n},x] && GtQ[d,0] && PosQ[e]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && gtq!(d__, 0)
                && posq!(e__)
        },
        rhs: {
            let rt_e = rubi_rt(&e__, 2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let inverse = (&rt_e * x_ / d__.sqrt()).asinh();
            let recursive_integrand = &inverse / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&inverse * logarithmic / &rt_e), x_)
                    - rubi_star(&b__ * &n_ / rt_e, recursive)
        },
    ));
}

fn push_rules_rule_2763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2763,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          ArcSin[Rt[-e,2]*x/Sqrt[d]]*(a+b*Log[c*x^n])/Rt[-e,2] - b*n/Rt[-e,2] \\[Star] Int[ArcSin[Rt[-e,2]*x/Sqrt[d]]/x,x] /;
        FreeQ[{a,b,c,d,e,n},x] && GtQ[d,0] && NegQ[e]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && gtq!(d__, 0)
                && negq!(e__)
        },
        rhs: {
            let rt_neg_e = rubi_rt(&(-&e__), 2);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let inverse = (&rt_neg_e * x_ / d__.sqrt()).asin();
            let recursive_integrand = &inverse / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&inverse * logarithmic / &rt_neg_e), x_)
                    - rubi_star(&b__ * &n_ / rt_neg_e, recursive)
        },
    ));
}

fn push_rules_rule_2764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2764,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Sqrt[1+e/d*x^2]/Sqrt[d+e*x^2] \\[Star] Int[(a+b*Log[c*x^n])/Sqrt[1+e/d*x^2],x] /;
        FreeQ[{a,b,c,d,e,n},x] && Not[GtQ[d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && !gtq!(d__, 0)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(2);
            let normalized = Atom::num(1) + &e__ * x_.pow(2) / &d__;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = logarithmic / normalized.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(normalized.sqrt(), recursive / base.sqrt())
        },
    ));
}

fn push_rules_rule_2765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, d2__, e1__, e2__, n_, x_);
    rules.push(rubi_rule!(
        order: 2765,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          Sqrt[1+e1*e2/(d1*d2)*x^2]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]) \\[Star] Int[(a+b*Log[c*x^n])/Sqrt[1+e1*e2/(d1*d2)*x^2],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[d2*e1+d1*e2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log())
            / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt()),
        with: [a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [a__, b__, c__, n_, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
        },
        rhs: {
            let denominator = &d1__ * &d2__;
            let first = &d1__ + &e1__ * x_;
            let second = &d2__ + &e2__ * x_;
            let normalized = Atom::num(1) + &e1__ * &e2__ * x_.pow(2) / &denominator;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = logarithmic / normalized.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(normalized.sqrt(), recursive / (first.sqrt() * second.sqrt()))
        },
    ));
}

fn push_rules_rule_2766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2766,
        source: "Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^r)^q,x]},
          (a+b*Log[c*x^n]) \\[Star] u - b*n \\[Star] Int[SimplifyIntegrand[u/x,x],x] /;
         EqQ[r,1] && IntegerQ[q-1/2] || EqQ[r,2] && EqQ[q,-1] || InverseFunctionFreeQ[u,x]] /;
        FreeQ[{a,b,c,d,e,n,q,r},x] && IntegerQ[2*q] && IntegerQ[r]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, r_, q_, a__, b__, c__, n_, x_],
        optional: [e__, r_, q_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_, r_], x_)
                && integerq!(Atom::num(2) * &q_)
                && integerq!(r_)
                && rubi_int_hide_logarithm_condition(
                    &(&d__ + &e__ * x_.pow(&r_)).pow(&q_),
                    x_,
                    (eqq!(r_, 1) && integerq!(&q_ - Atom::num(1) / Atom::num(2)))
                        || (eqq!(r_, 2) && eqq!(q_, -1)),
                )
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&r_);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let u = rubi_int_hide(&base.pow(&q_), x_).rubi_rhs();

            let recursive_integrand = rubi_simplify_integrand(&(&u / x_), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2767,
        source: "Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,(d+e*x^r)^q,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n,p,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IGtQ[p,0] && IntegerQ[r])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, r_, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_, r_], x_)
                && integerq!(q_)
                && (gtq!(q_, 0) || (igtq!(p_, 0) && integerq!(r_)))
                && {
                    let base_power = (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
                    let log_power = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
                    rubi_expand_integrand_product_sum(&log_power, &base_power, x_).is_some()
                }
        },
        rhs: {
            let base_power = (&d__ + &e__ * x_.pow(&r_)).pow(&q_);
            let log_power = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);
            let u = rubi_expand_integrand_product_sum(&log_power, &base_power, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2768(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2768,
        source: "Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, r_, q_, a__, b__, c__, n_, p_, x_],
        optional: [e__, r_, q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(&r_)).pow(&q_)
                    * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2769(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, q_, u__, x_);
    let rule = rubi_rule!(
        order: 2769,
        source: "Int[u_^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^q*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__.pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [u__, q_, a__, b__, c__, n_, p_, x_],
        optional: [q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && rubi_binomial_q(&u__, x_)
                && !rubi_binomial_match_q(&u__, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let recursive_integrand =
                expanded_u.pow(&q_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).log()) / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}
