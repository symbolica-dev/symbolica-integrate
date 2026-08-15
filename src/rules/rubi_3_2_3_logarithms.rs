use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2978(rules);
    push_rules_rule_2979(rules);
    push_rules_rule_2980(rules);
    push_rules_rule_2981(rules);
    push_rules_rule_2982(rules);
    push_rules_rule_2983(rules);
    push_rules_rule_2984(rules);
    push_rules_rule_2985(rules);
    push_rules_rule_2986(rules);
    push_rules_rule_2987(rules);
    push_rules_rule_2988(rules);
    push_rules_rule_2989(rules);
    push_rules_rule_2990(rules);
    push_rules_rule_2991(rules);
    push_rules_rule_2992(rules);
    push_rules_rule_2993(rules);
    push_rules_rule_2994(rules);
    push_rules_rule_2995(rules);
    push_rules_rule_2996(rules);
    push_rules_rule_2997(rules);
}

fn push_rules_rule_2978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, q_, r_, s_, u__, x_);
    rules.push(rubi_rule!(
        order: 2978,
        source: "Int[u_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          Int[u*Log[e*(b^p*f/d^p*(c+d*x)^(p+q))^r]^s,x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && EqQ[b*c-a*d,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__
            * (e__
                * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_),
        with: [u__, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [u__, e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_, s_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed_product =
                b__.pow(&p_) * &f__ / d__.pow(&p_) * (&c__ + &d__ * x_).pow(&p_ + &q_);
            let transformed_log_arg = &e__ * transformed_product.pow(&r_);
            let recursive_integrand = &u__ * transformed_log_arg.log().pow(&s_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, q_, r_, s_, x_);
    rules.push(rubi_rule!(
        order: 2979,
        source: "Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          (a+b*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/b -
          r*s*(p+q) \\[Star] Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1),x] +
          q*r*s*(b*c-a*d)/b \\[Star] Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && NeQ[p+q,0] && IGtQ[s,0] && LtQ[s,4]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_),
        with: [e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_, s_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&p_ + &q_, 0)
                && igtq!(s_, 0)
                && ltq!(s_, 4)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let lowered_logarithmic = logarithmic.pow(&s_ - 1);
            let first_recursive = rubi_rhs_int(&lowered_logarithmic, x_);
            let second_recursive = rubi_rhs_int(&(&lowered_logarithmic / &rhs), x_);

            rubi_simp(&(lhs * logarithmic.pow(&s_) / &b__), x_)
                    + rubi_star(&q_ * &r_ * &s_ * determinant / &b__, second_recursive)
                    - rubi_star(&r_ * &s_ * (&p_ + &q_), first_recursive)
        },
    ));
}

fn push_rules_rule_2980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2980,
        source: "Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/(g_.+h_.*x_),x_Symbol] :=
          Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/h -
          b*p*r/h \\[Star] Int[Log[g+h*x]/(a+b*x),x] -
          d*q*r/h \\[Star] Int[Log[g+h*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_)).log()
            / (g__ + h__ * x_),
        with: [e__, f__, a__, b__, p_, c__, d__, q_, r_, g__, h__, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let linear_log = linear.log();
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_recursive = rubi_rhs_int(&(&linear_log / &lhs), x_);
            let second_recursive = rubi_rhs_int(&(&linear_log / &rhs), x_);

            rubi_simp(&(&linear_log * logarithmic / &h__), x_)
                    - rubi_star(&b__ * &p_ * &r_ / &h__, first_recursive)
                    - rubi_star(&d__ * &q_ * &r_ / &h__, second_recursive)
        },
    ));
}

fn push_rules_rule_2981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2981,
        source: "Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
          (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(h*(m+1)) -
          b*p*r/(h*(m+1)) \\[Star] Int[(g+h*x)^(m+1)/(a+b*x),x] -
          d*q*r/(h*(m+1)) \\[Star] Int[(g+h*x)^(m+1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r},x] && NeQ[b*c-a*d,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
                .log(),
        with: [g__, h__, m_, e__, f__, a__, b__, p_, c__, d__, q_, r_, x_],
        optional: [g__, h__, m_, e__, f__, a__, b__, c__, d__, q_, r_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let raised_linear = linear.pow(&m_ + 1);
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_recursive = rubi_rhs_int(&(&raised_linear / &lhs), x_);
            let second_recursive = rubi_rhs_int(&(&raised_linear / &rhs), x_);
            let denominator = &h__ * (&m_ + 1);

            rubi_simp(&(&raised_linear * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &p_ * &r_ / &denominator, first_recursive)
                    - rubi_star(&d__ * &q_ * &r_ / denominator, second_recursive)
        },
    ));
}

fn push_rules_rule_2982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2982,
        source: "Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^2/(g_.+h_.*x_),x_Symbol] :=
          Int[(Log[(a+b*x)^(p*r)]+Log[(c+d*x)^(q*r)])^2/(g+h*x),x] +
          (Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]-Log[(a+b*x)^(p*r)]-Log[(c+d*x)^(q*r)])*
            (2 \\[Star] Int[Log[(c+d*x)^(q*r)]/(g+h*x),x] +
             Int[(Log[(a+b*x)^(p*r)]-Log[(c+d*x)^(q*r)]+Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r])/(g+h*x),x]) /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[b*g-a*h,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, a__, b__, p_, c__, d__, q_, r_, g__, h__, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &g__ - &a__ * &h__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let pr = &p_ * &r_;
            let qr = &q_ * &r_;
            let lhs_log = lhs.pow(&pr).log();
            let rhs_log = rhs.pow(&qr).log();
            let full_log = (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_integrand = (&lhs_log + &rhs_log).pow(2) / &linear;
            let second_integrand = &rhs_log / &linear;
            let third_integrand = (&lhs_log - &rhs_log + &full_log) / &linear;
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);
            let third_recursive = rubi_rhs_int(&third_integrand, x_);

            first_recursive
                    + (&full_log - &lhs_log - &rhs_log)
                        * (rubi_star(Atom::num(2), second_recursive) + third_recursive)
        },
    ));
}

fn push_rules_rule_2983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2983,
        source: "Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^2/(g_.+h_.*x_),x_Symbol] :=
          Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^2/h -
          2*b*p*r/h \\[Star] Int[Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(a+b*x),x] -
          2*d*q*r/h \\[Star] Int[Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, a__, b__, p_, c__, d__, q_, r_, g__, h__, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let linear_log = linear.log();
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_integrand = &linear_log * &logarithmic / &lhs;
            let second_integrand = &linear_log * &logarithmic / &rhs;
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(linear_log * logarithmic.pow(2) / &h__), x_)
                    - rubi_star(Atom::num(2) * &b__ * &p_ * &r_ / &h__, first_recursive)
                    - rubi_star(Atom::num(2) * &d__ * &q_ * &r_ / &h__, second_recursive)
        },
    ));
}

fn push_rules_rule_2984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, r_, s_, x_
    );
    rules.push(rubi_rule!(
        order: 2984,
        source: "Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_,x_Symbol] :=
          (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(h*(m+1)) -
          b*p*r*s/(h*(m+1)) \\[Star] Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(a+b*x),x] -
          d*q*r*s/(h*(m+1)) \\[Star] Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
                .log()
                .pow(s_),
        with: [g__, h__, m_, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [g__, h__, m_, e__, f__, a__, b__, c__, d__, q_, r_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, r_, s_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(s_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let raised_linear = linear.pow(&m_ + 1);
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let lowered_logarithmic = logarithmic.pow(&s_ - 1);
            let first_integrand = &raised_linear * &lowered_logarithmic / &lhs;
            let second_integrand = &raised_linear * &lowered_logarithmic / &rhs;
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);
            let denominator = &h__ * (&m_ + 1);

            rubi_simp(&(&raised_linear * logarithmic.pow(&s_) / &denominator), x_)
                    - rubi_star(&b__ * &p_ * &r_ * &s_ / &denominator, first_recursive)
                    - rubi_star(&d__ * &q_ * &r_ * &s_ / denominator, second_recursive)
        },
    ));
}

fn push_rules_rule_2985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, m_, n_, p_, q_, r_, s__, t__, x_
    );
    rules.push(rubi_rule!(
        order: 2985,
        source: "Int[(s_.+t_.*Log[i_.*(g_.+h_.*x_)^n_.])^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/(j_.+k_.*x_),x_Symbol] :=
          (s+t*Log[i*(g+h*x)^n])^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(k*n*t*(m+1)) -
          b*p*r/(k*n*t*(m+1)) \\[Star] Int[(s+t*Log[i*(g+h*x)^n])^(m+1)/(a+b*x),x] -
          d*q*r/(k*n*t*(m+1)) \\[Star] Int[(s+t*Log[i*(g+h*x)^n])^(m+1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,s,t,m,n,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[h*j-g*k,0] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (s__ + t__ * (i__ * (g__ + h__ * x_).pow(n_)).log()).pow(m_)
            * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
                .log()
            / (j__ + k__ * x_),
        with: [s__, t__, i__, g__, h__, n_, m_, e__, f__, a__, b__, p_, c__, d__, q_, r_, j__, k__, x_],
        optional: [s__, t__, i__, g__, h__, n_, m_, e__, f__, a__, b__, c__, d__, q_, r_, j__, k__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && freeq!([j__, k__, s__, t__, m_, n_, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&h__ * &j__ - &g__ * &k__, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let log_power_base = &s__ + &t__ * (&i__ * linear.pow(&n_)).log();
            let raised_log_power = log_power_base.pow(&m_ + 1);
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let denominator = &k__ * &n_ * &t__ * (&m_ + 1);
            let first_recursive = rubi_rhs_int(&(&raised_log_power / &lhs), x_);
            let second_recursive = rubi_rhs_int(&(&raised_log_power / &rhs), x_);

            rubi_simp(&(&raised_log_power * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &p_ * &r_ / &denominator, first_recursive)
                    - rubi_star(&d__ * &q_ * &r_ / denominator, second_recursive)
        },
    ));
}

fn push_rules_rule_2986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, n_, p_, q_, r_, s__, t__, x_
    );
    rules.push(rubi_rule!(
        order: 2986,
        source: "Int[(s_.+t_.*Log[i_.*(g_.+h_.*x_)^n_.])*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/(j_.+k_.*x_),x_Symbol] :=
          (Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]-Log[(a+b*x)^(p*r)]-Log[(c+d*x)^(q*r)]) \\[Star] Int[(s+t*Log[i*(g+h*x)^n])/(j+k*x),x] +
          Int[(Log[(a+b*x)^(p*r)]*(s+t*Log[i*(g+h*x)^n]))/(j+k*x),x] +
          Int[(Log[(c+d*x)^(q*r)]*(s+t*Log[i*(g+h*x)^n]))/(j+k*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,s,t,n,p,q,r},x] && NeQ[b*c-a*d,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (s__ + t__ * (i__ * (g__ + h__ * x_).pow(n_)).log())
            * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
                .log()
            / (j__ + k__ * x_),
        with: [s__, t__, i__, g__, h__, n_, e__, f__, a__, b__, p_, c__, d__, q_, r_, j__, k__, x_],
        optional: [s__, t__, i__, g__, h__, n_, e__, f__, a__, b__, c__, d__, q_, r_, j__, k__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && freeq!([j__, k__, s__, t__, n_, p_, q_, r_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let denominator = &j__ + &k__ * x_;
            let logarithmic_base = &s__ + &t__ * (&i__ * linear.pow(&n_)).log();
            let pr = &p_ * &r_;
            let qr = &q_ * &r_;
            let lhs_log = lhs.pow(&pr).log();
            let rhs_log = rhs.pow(&qr).log();
            let full_log = (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_recursive = rubi_rhs_int(&(&logarithmic_base / &denominator), x_);
            let second_recursive =
                rubi_rhs_int(&(&lhs_log * &logarithmic_base / &denominator), x_);
            let third_recursive =
                rubi_rhs_int(&(&rhs_log * &logarithmic_base / &denominator), x_);

            rubi_star(&full_log - &lhs_log - &rhs_log, first_recursive) + second_recursive
                    + third_recursive
        },
    ));
}

fn push_rules_rule_2987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, m_, n_, p_, q_, r_, s__, t__, u_, x_
    );
    rules.push(rubi_rule!(
        order: 2987,
        source: "Int[(s_.+t_.*Log[i_.*(g_.+h_.*x_)^n_.])^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^u_./(j_.+k_.*x_),x_Symbol] :=
          Unintegrable[(s+t*Log[i*(g+h*x)^n])^m*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^u/(j+k*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,s,t,m,n,p,q,r,u},x] && NeQ[b*c-a*d,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (s__ + t__ * (i__ * (g__ + h__ * x_).pow(n_)).log()).pow(m_)
            * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
                .log()
                .pow(u_)
            / (j__ + k__ * x_),
        with: [s__, t__, i__, g__, h__, n_, m_, e__, f__, a__, b__, p_, c__, d__, q_, r_, u_, j__, k__, x_],
        optional: [s__, t__, i__, g__, h__, n_, m_, e__, f__, a__, b__, c__, d__, q_, r_, u_, j__, k__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && freeq!([j__, k__, s__, t__, m_, n_, p_, q_, r_, u_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let integrand = (&s__ + &t__ * (&i__ * (&g__ + &h__ * x_).pow(&n_)).log()).pow(&m_)
                * (&e__
                    * (&f__
                        * (&a__ + &b__ * x_).pow(&p_)
                        * (&c__ + &d__ * x_).pow(&q_))
                    .pow(&r_))
                .log()
                .pow(&u_)
                / (&j__ + &k__ * x_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, q_, r_, s_, u__, v_, x_);
    rules.push(rubi_rule!(
        order: 2988,
        source: "Int[u_*Log[v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          With[{g=Simplify[(v-1)*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
          -h*PolyLog[2,1-v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) +
          h*p*r*s \\[Star] Int[PolyLog[2,1-v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
         FreeQ[{g,h},x]] /;
        FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__
            * Atom::var(v_).log()
            * (e__
                * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_),
        with: [u__, v_, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_, s_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(s_, 0)
                && eqq!(&p_ + &q_, 0)
                && {
                    let lhs = &a__ + &b__ * x_;
                    let rhs = &c__ + &d__ * x_;
                    let with_g = rubi_simplify(&((&v_ - 1) * &rhs / &lhs));
                    let with_h = rubi_simplify(&(&u__ * &lhs * &rhs));
                    freeq!([with_g, with_h], x_)
                }
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let with_h = rubi_simplify(&(&u__ * &lhs * &rhs));
            let determinant = &b__ * &c__ - &a__ * &d__;
            let polylogarithm = (Atom::num(1) - &v_).polylog(2);
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let recursive_integrand =
                &polylogarithm * logarithmic.pow(&s_ - 1) / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&with_h * &polylogarithm * logarithmic.pow(&s_) / &determinant),
                    x_,
                ) + rubi_star(with_h * &p_ * &r_ * &s_ / determinant, recursive)
        },
    ));
}

fn push_rules_rule_2989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, p_, q_, r_, s_, t_, u_, v__, x_
    );
    rules.push(rubi_rule!(
        order: 2989,
        source: "Int[v_*Log[i_.*(j_.*(g_.+h_.*x_)^t_.)^u_.]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          With[{k=Simplify[v*(a+b*x)*(c+d*x)]},
          k*Log[i*(j*(g+h*x)^t)^u]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(p*r*(s+1)*(b*c-a*d)) -
          k*h*t*u/(p*r*(s+1)*(b*c-a*d)) \\[Star] Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(g+h*x),x] /;
         FreeQ[k,x]] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s,t,u},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && NeQ[s,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: v__
            * (i__ * (j__ * (g__ + h__ * x_).pow(t_)).pow(u_)).log()
            * (e__
                * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_),
        with: [v__, i__, j__, g__, h__, t_, u_, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [i__, j__, g__, h__, t_, u_, e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && freeq!([j__, p_, q_, r_, s_, t_, u_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&p_ + &q_, 0)
                && neq!(s_, -1)
                && {
                    let lhs = &a__ + &b__ * x_;
                    let rhs = &c__ + &d__ * x_;
                    let with_k = rubi_simplify(&(&v__ * &lhs * &rhs));
                    is_free_of(&with_k, x_)
                }
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear = &g__ + &h__ * x_;
            let with_k = rubi_simplify(&(&v__ * &lhs * &rhs));
            let determinant = &b__ * &c__ - &a__ * &d__;
            let denominator = &p_ * &r_ * (&s_ + 1) * &determinant;
            let linear_log = (&i__ * (&j__ * linear.pow(&t_)).pow(&u_)).log();
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let recursive_integrand = logarithmic.pow(&s_ + 1) / &linear;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&with_k * linear_log * logarithmic.pow(&s_ + 1) / &denominator),
                    x_,
                ) - rubi_star(with_k * &h__ * &t_ * &u_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, s_, u__, v_, x_
    );
    rules.push(rubi_rule!(
        order: 2990,
        source: "Int[u_*PolyLog[n_,v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          With[{g=Simplify[v*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
          h*PolyLog[n+1,v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) -
          h*p*r*s \\[Star] Int[PolyLog[n+1,v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
         FreeQ[{g,h},x]] /;
        FreeQ[{a,b,c,d,e,f,n,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__
            * Atom::var(v_).polylog(n_)
            * (e__
                * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_),
        with: [u__, n_, v_, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, s_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(s_, 0)
                && eqq!(&p_ + &q_, 0)
                && {
                    let lhs = &a__ + &b__ * x_;
                    let rhs = &c__ + &d__ * x_;
                    let with_g = rubi_simplify(&(&v_ * &rhs / &lhs));
                    let with_h = rubi_simplify(&(&u__ * &lhs * &rhs));
                    freeq!([with_g, with_h], x_)
                }
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let with_h = rubi_simplify(&(&u__ * &lhs * &rhs));
            let determinant = &b__ * &c__ - &a__ * &d__;
            let raised_polylogarithm = v_.polylog(&n_ + 1);
            let logarithmic =
                (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let recursive_integrand =
                &raised_polylogarithm * logarithmic.pow(&s_ - 1) / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&with_h * &raised_polylogarithm * logarithmic.pow(&s_) / &determinant),
                    x_,
                ) - rubi_star(with_h * &p_ * &r_ * &s_ / determinant, recursive)
        },
    ));
}

fn push_rules_rule_2991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
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
        order: 2991,
        source: "Int[(a_.+b_.*Log[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
          2*e*g/(C*(e*f-d*g)) \\[Star] Subst[Int[(a+b*Log[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,C,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__
            + b__ * (c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt()).log())
        .pow(n_)
            / (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, capital_c__, n_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&capital_b__ * &e__ * &g__ - &capital_c__ * (&e__ * &f__ + &d__ * &g__), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&a__ + &b__ * (&c__ * &sub_atom).log()).pow(&n_) / &sub_atom;
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();
            let coefficient =
                Atom::num(2) * &e__ * &g__ / (&capital_c__ * (&e__ * &f__ - &d__ * &g__));

            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_c__,
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
        order: 2992,
        source: "Int[(a_.+b_.*Log[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+C_.*x_^2),x_Symbol] :=
          g/(C*f) \\[Star] Subst[Int[(a+b*Log[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,C,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__
            + b__ * (c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt()).log())
        .pow(n_)
            / (capital_a__ + capital_c__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_c__, n_], x_)
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&a__ + &b__ * (&c__ * &sub_atom).log()).pow(&n_) / &sub_atom;
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();
            let coefficient = &g__ / (&capital_c__ * &f__);

            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, q_, r_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 2993,
        source: "Int[RFx_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
          p*r \\[Star] Int[RFx*Log[a+b*x],x] +
          q*r \\[Star] Int[RFx*Log[c+d*x],x] -
          (p*r*Log[a+b*x]+q*r*Log[c+d*x] - Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]) \\[Star] Int[RFx,x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && RationalFunctionQ[RFx,x] && NeQ[b*c-a*d,0] &&
          Not[MatchQ[RFx,u_.*(a+b*x)^m_.*(c+d*x)^n_. /; IntegersQ[m,n]]]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: rfx__
            * (e__
                * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log(),
        with: [rfx__, e__, f__, a__, b__, p_, c__, d__, q_, r_, x_],
        optional: [rfx__, e__, f__, a__, b__, c__, d__, q_, r_, p_],
        when: {
            let lhs = &a__ + &b__ * x_;

            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !rubi_match_optional_multiplier_affine_integer_power(&rfx__, &lhs)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let full_log = (&e__ * (&f__ * lhs.pow(&p_) * rhs.pow(&q_)).pow(&r_)).log();
            let first_recursive = rubi_rhs_int(&(&rfx__ * lhs.log()), x_);
            let second_recursive = rubi_rhs_int(&(&rfx__ * rhs.log()), x_);
            let third_recursive = rubi_rhs_int(&rfx__, x_);

            rubi_star(&p_ * &r_, first_recursive)
                    + rubi_star(&q_ * &r_, second_recursive)
                    - rubi_star(&p_ * &r_ * lhs.log() + &q_ * &r_ * rhs.log() - full_log, third_recursive)
        },
    ));
}

fn push_rules_rule_2994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, rfx__, s_, x_);
    rules.push(rubi_rule!(
        order: 2994,
        source: "Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x] && IGtQ[s,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [rfx__, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_, s_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(s_, 0)
                && {
                    let log_power = (&e__
                        * (&f__
                            * (a__ + b__ * x_).pow(&p_)
                            * (c__ + d__ * x_).pow(&q_))
                        .pow(&r_))
                    .log()
                    .pow(&s_);
                    rubi_expand_integrand_product_sum(&log_power, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let log_power =
                (&e__ * (&f__ * (a__ + b__ * x_).pow(&p_) * (c__ + d__ * x_).pow(&q_)).pow(&r_))
                    .log()
                    .pow(&s_);
            let u = rubi_expand_integrand_product_sum(&log_power, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, rfx__, s_, x_);
    rules.push(rubi_rule!(
        order: 2995,
        source: "Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
          Unintegrable[RFx*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [rfx__, e__, f__, a__, b__, p_, c__, d__, q_, r_, s_, x_],
        optional: [e__, f__, a__, b__, c__, d__, q_, r_, s_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_, s_], x_)
                && rubi_rational_function_q(&rfx__, x_)
        },
        rhs: {
            let integrand =
                &rfx__
                    * (&e__
                        * (&f__
                            * (&a__ + &b__ * x_).pow(&p_)
                            * (&c__ + &d__ * x_).pow(&q_))
                        .pow(&r_))
                    .log()
                    .pow(&s_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, f__, p_, q_, r_, s_, u__, v__, w__);
    rules.push(rubi_rule!(
        order: 2996,
        source: "Int[u_.*Log[e_.*(f_.*v_^p_.*w_^q_.)^r_.]^s_.,x_Symbol] :=
          Int[u*Log[e*(f*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q)^r]^s,x] /;
        FreeQ[{e,f,p,q,r,s},x] && LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]] && AlgebraicFunctionQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (e__ * (f__ * v__.pow(p_) * w__.pow(q_)).pow(r_)).log().pow(s_),
        with: [u__, e__, f__, v__, p_, w__, q_, r_, s_, x_],
        optional: [u__, e__, f__, q_, r_, s_, p_],
        when: {
            freeq!([e__, f__, p_, q_, r_, s_], x_)
                && rubi_linear_q_list(&[&v__, &w__], x_)
                && !rubi_linear_match_q_list(&[&v__, &w__], x_)
                && rubi_algebraic_function_q(&u__, x_, true)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let recursive_integrand =
                &u__ * (&e__ * (&f__ * expanded_v.pow(&p_) * expanded_w.pow(&q_)).pow(&r_))
                    .log()
                    .pow(&s_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, f__, g__, r_, s_, u__, v__, w__);
    rules.push(rubi_rule!(
        order: 2997,
        source: "Int[u_.*Log[e_.*(f_.*(g_+v_./w_))^r_.]^s_.,x_Symbol] :=
          Int[u*Log[e*(f*ExpandToSum[v+g*w,x]/ExpandToSum[w,x])^r]^s,x] /;
        FreeQ[{e,f,g,r,s},x] && LinearQ[w,x] && (FreeQ[v,x] || LinearQ[v,x]) && AlgebraicFunctionQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (e__ * (f__ * (g__ + v__ / w__)).pow(r_)).log().pow(s_),
        with: [u__, e__, f__, g__, v__, w__, r_, s_, x_],
        optional: [u__, e__, f__, v__, r_, s_],
        when: {
            freeq!([e__, f__, g__, r_, s_], x_)
                && rubi_linear_q(&w__, x_)
                && (freeq!(v__, x_) || rubi_linear_q(&v__, x_))
                && rubi_algebraic_function_q(&u__, x_, true)
        },
        rhs: {
            let numerator = rubi_expand_to_sum(&(&v__ + &g__ * &w__), x_);
            let denominator = rubi_expand_to_sum(&w__, x_);
            let recursive_integrand =
                &u__ * (&e__ * (&f__ * numerator / denominator).pow(&r_))
                    .log()
                    .pow(&s_);

            rubi_rhs_int(&recursive_integrand, x_)
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
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
        .log()
        .pow(2)
        / (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let rfx__ = symbols.rfx__;
    let s_ = symbols.s_;
    let x_ = symbols.x_;
    rfx__
        * (e__ * (f__ * (a__ + b__ * x_).pow(p_) * (c__ + d__ * x_).pow(q_)).pow(r_))
            .log()
            .pow(s_)
}
