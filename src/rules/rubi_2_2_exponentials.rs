use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2620(rules);
    push_rules_rule_2621(rules);
    push_rules_rule_2622(rules);
    push_rules_rule_2623(rules);
}

fn push_rules_rule_2620(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2620,
        source: "Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_./(a_+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.),x_Symbol] :=
          (c+d*x)^m/(b*f*g*n*Log[F])*Log[1+b*(F^(g*(e+f*x)))^n/a] -
          d*m/(b*f*g*n*Log[F]) \\[Star] Int[(c+d*x)^(m-1)*Log[1+b*(F^(g*(e+f*x)))^n/a],x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_)
            * capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_)
            / (a__ + b__ * capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_)),
        with: [c__, d__, m_, capital_f_, g__, e__, f__, n_, a__, b__, x_],
        optional: [c__, d__, m_, g__, e__, f__, b__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && igtq!(m_, 0)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let logarithm = (Atom::num(1) + &b__ * &exponential / &a__).log();
            let denominator = &b__ * &f__ * &g__ * &n_ * capital_f_.log();
            let recursive_integrand = affine.pow(&m_ - 1) * &logarithm;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let first = rubi_simp(&(affine.pow(&m_) * &logarithm / &denominator), x_);
            let second = rubi_simp(&(&d__ * &m_ * recursive / &denominator), x_);

            rubi_simp(&(first), x_) - rubi_star(Atom::num(1), second)
        },
    ));
}
fn push_rules_rule_2621(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_
    );
    let exponential = capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_);
    rules.push(rubi_rule!(
        order: 2621,
        source: "Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
          (c+d*x)^m*(a+b*(F^(g*(e+f*x)))^n)^(p+1)/(b*f*g*n*(p+1)*Log[F]) -
          d*m/(b*f*g*n*(p+1)*Log[F]) \\[Star] Int[(c+d*x)^(m-1)*(a+b*(F^(g*(e+f*x)))^n)^(p+1),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,m,n,p},x] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * &exponential * (a__ + b__ * &exponential).pow(p_),
        with: [c__, d__, m_, capital_f_, g__, e__, f__, n_, a__, b__, p_, x_],
        optional: [c__, d__, m_, g__, e__, f__, a__, b__, p_, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(p_, -Atom::num(1))
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let binomial = &a__ + &b__ * &exponential;
            let raised_p = &p_ + 1;
            let denominator = &b__ * &f__ * &g__ * &n_ * &raised_p * capital_f_.log();
            let recursive_integrand = affine.pow(&m_ - 1) * binomial.pow(&raised_p);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&m_) * binomial.pow(&raised_p) / &denominator),
                    x_,
                ) - rubi_star(&d__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2622(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_
    );
    let exponential = capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_);
    rules.push(rubi_rule!(
        order: 2622,
        source: "Int[(c_.+d_.*x_)^m_.*(F_^(g_.*(e_.+f_.*x_)))^n_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
        FreeQ[{F,a,b,c,d,e,f,g,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * &exponential * (a__ + b__ * &exponential).pow(p_),
        with: [c__, d__, m_, capital_f_, g__, e__, f__, n_, a__, b__, p_, x_],
        optional: [c__, d__, m_, g__, e__, f__, a__, b__, p_, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&c__ + &d__ * x_).pow(&m_)
                * capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_)
                * (&a__
                    + &b__ * capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_))
                .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2623(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, m_, n_, p_, q_, x_, e__, f__, g__, h__, i__,
        j__, k__
    );
    rules.push(rubi_rule!(
        order: 2623,
        source: "Int[(c_.+d_.*x_)^m_.*(k_.*G_^(j_.*(h_.+i_.*x_)))^q_.*(a_.+b_.*(F_^(g_.*(e_.+f_.*x_)))^n_.)^p_.,x_Symbol] :=
          (k*G^(j*(h+i*x)))^q/(F^(g*(e+f*x)))^n \\[Star] Int[(c+d*x)^m*(F^(g*(e+f*x)))^n*(a+b*(F^(g*(e+f*x)))^n)^p,x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,i,j,k,m,n,p,q},x] && EqQ[f*g*n*Log[F]-i*j*q*Log[G],0] && NeQ[(k*G^(j*(h+i*x)))^q-(F^(g*(e+f*x)))^n,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_)
            * (k__ * capital_g_.pow(j__ * (h__ + i__ * x_))).pow(q_)
            * (a__ + b__ * capital_f_.pow(g__ * (e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [c__, d__, m_, k__, capital_g_, j__, h__, i__, q_, a__, b__, capital_f_, g__, e__, f__, n_, p_, x_],
        optional: [c__, d__, m_, k__, j__, h__, i__, q_, a__, b__, g__, e__, f__, n_, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && freeq!([h__, i__, j__, k__, m_, n_, p_, q_], x_)
                && eqq!(
                    &f__ * &g__ * &n_ * capital_f_.log() - &i__ * &j__ * &q_ * capital_g_.log(),
                    0
                )
                && {
                    let target_exponential =
                        capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
                    let other_exponential =
                        (&k__ * capital_g_.pow(&j__ * (&h__ + &i__ * x_))).pow(&q_);
                    neq!(other_exponential - target_exponential, 0)
                }
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let target_exponential = capital_f_.pow(&g__ * (&e__ + &f__ * x_)).pow(&n_);
            let other_exponential =
                (&k__ * capital_g_.pow(&j__ * (&h__ + &i__ * x_))).pow(&q_);
            let binomial = &a__ + &b__ * &target_exponential;
            let recursive_integrand = affine.pow(&m_) * &target_exponential * binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(other_exponential, recursive / target_exponential)
        },
    ));
}
