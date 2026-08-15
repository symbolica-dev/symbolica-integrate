use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7140(rules);
    push_rules_rule_7141(rules);
    push_rules_rule_7142(rules);
    push_rules_rule_7143(rules);
    push_rules_rule_7144(rules);
    push_rules_rule_7145(rules);
    push_rules_rule_7146(rules);
    push_rules_rule_7147(rules);
    push_rules_rule_7148(rules);
    push_rules_rule_7149(rules);
    push_rules_rule_7150(rules);
    push_rules_rule_7151(rules);
    push_rules_rule_7152(rules);
    // Rubi 8.8 block 14 is commented out in the markdown source.

    push_rules_rule_7153(rules);
    push_rules_rule_7154(rules);
    push_rules_rule_7155(rules);
    push_rules_rule_7156(rules);
    push_rules_rule_7157(rules);
    push_rules_rule_7158(rules);
    push_rules_rule_7159(rules);
    push_rules_rule_7160(rules);
    push_rules_rule_7161(rules);
    push_rules_rule_7162(rules);
    push_rules_rule_7163(rules);
    push_rules_rule_7164(rules);
    push_rules_rule_7165(rules);
}

fn push_rules_rule_7140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7140,
        source: "Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          x*PolyLog[n,a*(b*x^p)^q] - p*q \\[Star] Int[PolyLog[n-1,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,p,q},x] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [n_, a__, b__, p_, q_, x_],
        optional: [a__, b__, p_, q_],
        when: { freeq!([a__, b__, p_, q_], x_) && gtq!(n_, 0) },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            rubi_simp(&(x_ * &argument.polylog(&n_)), x_)
                    - rubi_star(&p_ * &q_, rubi_rhs_int(&argument.polylog(n_ - Atom::num(1)), x_))
        },
    ));
}

fn push_rules_rule_7141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7141,
        source: "Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          x*PolyLog[n+1,a*(b*x^p)^q]/(p*q) - 1/(p*q) \\[Star] Int[PolyLog[n+1,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,p,q},x] && LtQ[n,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [n_, a__, b__, p_, q_, x_],
        optional: [a__, b__, p_, q_],
        when: { freeq!([a__, b__, p_, q_], x_) && ltq!(n_, -1) },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            let denominator = &p_ * &q_;
            rubi_simp(&(x_ * &argument.polylog(&n_ + Atom::num(1)) / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&argument.polylog(n_ + Atom::num(1)), x_))
        },
    ));
}

fn push_rules_rule_7142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7142,
        source: "Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          Unintegrable[PolyLog[n,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [n_, a__, b__, p_, q_, x_],
        optional: [a__, b__, p_, q_],
        when: { freeq!([a__, b__, n_, p_, q_], x_) },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            rubi_unintegrable(argument.polylog(n_), x_)
        },
    ));
}

fn push_rules_rule_7143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7143,
        source: "Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.]/(d_.+e_.*x_),x_Symbol] :=
          PolyLog[n+1,c*(a+b*x)^p]/(e*p) /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,a*e]",
        desc: "Primitive rule",
        refs: [],
        pattern: (c__ * (a__ + b__ * x_).pow(p_)).polylog(n_) / (d__ + e__ * x_),
        with: [n_, c__, a__, b__, p_, d__, e__, x_],
        optional: [c__, a__, b__, p_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_) && eqq!(&b__ * &d__, &a__ * &e__)
        },
        rhs: {
            let argument = c__ * (&a__ + &b__ * x_).pow(&p_);
            rubi_simp(&(argument.polylog(n_ + Atom::num(1)) / (e__ * p_)), x_)
        },
    ));
}

fn push_rules_rule_7144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7144,
        source: "Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
          PolyLog[n+1,a*(b*x^p)^q]/(p*q) /;
        FreeQ[{a,b,n,p,q},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (a__ * (b__ * x_.pow(p_)).pow(q_)).polylog(n_) / x_,
        with: [n_, a__, b__, p_, q_, x_],
        optional: [a__, b__, p_, q_],
        when: { freeq!([a__, b__, n_, p_, q_], x_) },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            rubi_simp(&(argument.polylog(n_ + Atom::num(1)) / (p_ * q_)), x_)
        },
    ));
}

fn push_rules_rule_7145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7145,
        source: "Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          (d*x)^(m+1)*PolyLog[n,a*(b*x^p)^q]/(d*(m+1)) -
          p*q/(m+1) \\[Star] Int[(d*x)^m*PolyLog[n-1,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,d,m,p,q},x] && NeQ[m,-1] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, m_, n_, a__, b__, p_, q_, x_],
        optional: [d__, m_, a__, b__, p_, q_],
        when: {
            freeq!([a__, b__, d__, m_, p_, q_], x_)
                && neq!(m_, Atom::num(-1))
                && gtq!(n_, 0)
        },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            let scaled_power = (&d__ * x_).pow(&m_);
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1))
                    * &argument.polylog(&n_)
                    / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&p_ * &q_ / (m_ + Atom::num(1)), rubi_rhs_int(&(scaled_power * argument.polylog(n_ - Atom::num(1))), x_))
        },
    ));
}

fn push_rules_rule_7146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7146,
        source: "Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          (d*x)^(m+1)*PolyLog[n+1,a*(b*x^p)^q]/(d*p*q) -
          (m+1)/(p*q) \\[Star] Int[(d*x)^m*PolyLog[n+1,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,d,m,p,q},x] && NeQ[m,-1] && LtQ[n,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, m_, n_, a__, b__, p_, q_, x_],
        optional: [d__, m_, a__, b__, p_, q_],
        when: {
            freeq!([a__, b__, d__, m_, p_, q_], x_)
                && neq!(m_, Atom::num(-1))
                && ltq!(n_, -1)
        },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            let scaled_power = (&d__ * x_).pow(&m_);
            let denominator = &p_ * &q_;
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1))
                    * &argument.polylog(&n_ + Atom::num(1))
                    / (&d__ * &denominator)), x_)
                    - rubi_star((m_ + Atom::num(1)) / denominator, rubi_rhs_int(&(scaled_power * argument.polylog(n_ + Atom::num(1))), x_))
        },
    ));
}

fn push_rules_rule_7147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 7147,
        source: "Int[(d_.*x_)^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
          Unintegrable[(d*x)^m*PolyLog[n,a*(b*x^p)^q],x] /;
        FreeQ[{a,b,d,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, m_, n_, a__, b__, p_, q_, x_],
        optional: [d__, m_, a__, b__, p_, q_],
        when: { freeq!([a__, b__, d__, m_, n_, p_, q_], x_) },
        rhs: {
            let argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            rubi_unintegrable((&d__ * x_).pow(&m_) * argument.polylog(n_), x_)
        },
    ));
}

fn push_rules_rule_7148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 7148,
        source: "Int[Log[c_.*x_^m_.]^r_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
          Log[c*x^m]^r*PolyLog[n+1,a*(b*x^p)^q]/(p*q) -
          m*r/(p*q) \\[Star] Int[Log[c*x^m]^(r-1)*PolyLog[n+1,a*(b*x^p)^q]/x,x] /;
        FreeQ[{a,b,c,m,n,q,r},x] && GtQ[r,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * x_.pow(m_)).log().pow(r_) * (a__ * (b__ * x_.pow(p_)).pow(q_)).polylog(n_) / x_,
        with: [c__, m_, r_, n_, a__, b__, p_, q_, x_],
        optional: [c__, m_, a__, b__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, m_, n_, q_, r_], x_) && gtq!(r_, 0) },
        rhs: {
            let log_argument = (&c__ * x_.pow(&m_)).log();
            let polylog_argument = a__ * (b__ * x_.pow(&p_)).pow(&q_);
            let denominator = &p_ * &q_;
            rubi_simp(&(log_argument.pow(&r_) * &polylog_argument.polylog(&n_ + Atom::num(1)) / &denominator), x_)
                    - rubi_star(&m_ * &r_ / denominator, rubi_rhs_int(&(log_argument.pow(&r_ - 1) * polylog_argument.polylog(n_ + Atom::num(1)) / x_), x_))
        },
    ));
}

fn push_rules_rule_7149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7149,
        source: "Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
          x*PolyLog[n,c*(a+b*x)^p] -
          p \\[Star] Int[PolyLog[n-1,c*(a+b*x)^p],x] +
          a*p \\[Star] Int[PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x] /;
        FreeQ[{a,b,c,p},x] && GtQ[n,0]",
        desc: "Integration by parts and algebraic expansion",
        refs: [],
        pattern: (c__ * (a__ + b__ * x_).pow(p_)).polylog(n_),
        with: [n_, c__, a__, b__, p_, x_],
        optional: [c__, a__, b__, p_],
        when: { freeq!([a__, b__, c__, p_], x_) && gtq!(n_, 0) },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let argument = c__ * affine.pow(&p_);
            rubi_simp(&(x_ * &argument.polylog(&n_)), x_)
                    - rubi_star(&p_, rubi_rhs_int(&argument.polylog(&n_ - Atom::num(1)), x_))
                    + rubi_star(&a__ * &p_, rubi_rhs_int(&(argument.polylog(n_ - Atom::num(1)) / affine), x_))
        },
    ));
}

fn push_rules_rule_7150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 7150,
        source: "Int[PolyLog[2,c_.*(a_.+b_.*x_)]/(d_.+e_.*x_),x_Symbol] :=
          Log[1-a*c-b*c*x]*PolyLog[2,c*(a+b*x)]/e + b/e \\[Star] Int[Log[1-a*c-b*c*x]^2/(a+b*x),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*(b*d-a*e)+e,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * (&b__ * &d__ - &a__ * &e__) + &e__, 0)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let argument = &c__ * &affine;
            let log_term = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            rubi_simp(&(&log_term * argument.polylog(2) / &e__), x_)
                    + rubi_star(&b__ / e__, rubi_rhs_int(&(log_term.pow(2) / affine), x_))
        },
    ));
}

fn push_rules_rule_7151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 7151,
        source: "Int[PolyLog[2,c_.*(a_.+b_.*x_)]/(d_.+e_.*x_),x_Symbol] :=
          Log[d+e*x]*PolyLog[2,c*(a+b*x)]/e + b/e \\[Star] Int[Log[d+e*x]*Log[1-a*c-b*c*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c*(b*d-a*e)+e,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&c__ * (&b__ * &d__ - &a__ * &e__) + &e__, Atom::num(0))
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let denominator = d__ + &e__ * x_;
            let argument = &c__ * &affine;
            let log_denominator = denominator.log();
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            rubi_simp(&(&log_denominator * argument.polylog(2) / &e__), x_)
                    + rubi_star(&b__ / e__, rubi_rhs_int(&(log_denominator * log_argument / affine), x_))
        },
    ));
}

fn push_rules_rule_7152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 7152,
        source: "Int[(d_.+e_.*x_)^m_.*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          (d+e*x)^(m+1)*PolyLog[2,c*(a+b*x)]/(e*(m+1)) + b/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*Log[1-a*c-b*c*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [d__, e__, m_, c__, a__, b__, x_],
        optional: [d__, e__, m_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && neq!(m_, Atom::num(-1))
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let shifted = d__ + &e__ * x_;
            let argument = &c__ * &affine;
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            rubi_simp(&(shifted.pow(&m_ + Atom::num(1)) * argument.polylog(2)
                    / (&e__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ / (&e__ * (&m_ + Atom::num(1))), rubi_rhs_int(&(shifted.pow(m_ + Atom::num(1)) * log_argument / affine), x_))
        },
    ));
}

fn push_rules_rule_7153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7153,
        source: "Int[x_^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
          -(a^(m+1)-b^(m+1)*x^(m+1))*PolyLog[n,c*(a+b*x)^p]/((m+1)*b^(m+1)) +
          p/((m+1)*b^m) \\[Star] Int[ExpandIntegrand[PolyLog[n-1,c*(a+b*x)^p],(a^(m+1)-b^(m+1)*x^(m+1))/(a+b*x),x],x] /;
        FreeQ[{a,b,c,p},x] && GtQ[n,0] && IntegerQ[m] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (c__ * (a__ + b__ * x_).pow(p_)).polylog(n_),
        with: [m_, n_, c__, a__, b__, p_, x_],
        optional: [m_, c__, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && gtq!(n_, 0)
                && integerq!(m_)
                && neq!(m_, -1)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let argument = c__ * affine.pow(&p_);
            let quotient = (a__.pow(&m_ + 1) - b__.pow(&m_ + 1) * x_.pow(&m_ + 1)) / affine;
            let expanded = rubi_expand_integrand_product(&argument.polylog(&n_ - 1), &quotient, x_);
            rubi_simp(&(-(a__.pow(&m_ + 1) - b__.pow(&m_ + 1) * x_.pow(&m_ + 1)) * argument.polylog(&n_)
                    / ((&m_ + 1) * b__.pow(&m_ + 1))), x_)
                    + rubi_star(p_, rubi_rhs_int(&expanded, x_) / ((&m_ + 1) * b__.pow(&m_)))
        },
    ));
}

fn push_rules_rule_7154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, x_);
    rules.push(rubi_rule!(
        order: 7154,
        source: "Int[(g_.+h_.*Log[f_.*(d_.+e_.*x_)^n_.])*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          x*(g+h*Log[f*(d+e*x)^n])*PolyLog[2,c*(a+b*x)] +
          b \\[Star] Int[(g+h*Log[f*(d+e*x)^n])*Log[1-a*c-b*c*x]*ExpandIntegrand[x/(a+b*x),x],x] -
          e*h*n \\[Star] Int[PolyLog[2,c*(a+b*x)]*ExpandIntegrand[x/(d+e*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (g__ + h__ * (f__ * (d__ + e__ * x_).pow(n_)).log()) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [g__, h__, f__, d__, e__, n_, c__, a__, b__, x_],
        optional: [g__, h__, f__, d__, e__, n_, c__, a__, b__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_) },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let shifted = &d__ + &e__ * x_;
            let log_factor = &g__ + &h__ * (&f__ * shifted.pow(&n_)).log();
            let argument = &c__ * &affine;
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            let expanded_affine = rubi_expand_integrand(&(x_ / &affine), x_);
            let expanded_shifted = rubi_expand_integrand(&(x_ / shifted), x_);
            rubi_simp(&(x_ * &log_factor * &argument.polylog(2)), x_)
                    + rubi_star(b__, rubi_rhs_int(&(log_factor * log_argument * expanded_affine), x_))
                    - rubi_star(&e__ * &h__ * &n_, rubi_rhs_int(&(argument.polylog(2) * expanded_shifted), x_))
        },
    ));
}

fn push_rules_rule_7155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, e__, x_);
    rules.push(rubi_rule!(
        order: 7155,
        source: "Int[Log[1+e_.*x_]*PolyLog[2,c_.*x_]/x_,x_Symbol] :=
          -PolyLog[2,c*x]^2/2 /;
        FreeQ[{c,e},x] && EqQ[c+e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (Atom::num(1) + e__ * x_).log() * (c__ * x_).polylog(2) / x_,
        with: [e__, c__, x_],
        optional: [e__, c__],
        when: { freeq!([c__, e__], x_) && eqq!(&c__ + &e__, 0) },
        rhs: {
            let argument = &c__ * x_;
            rubi_simp(&(-argument.polylog(2).pow(2) / 2), x_)
        },
    ));
}

fn push_rules_rule_7156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, e__, g_, h__, x_);
    rules.push(rubi_rule!(
        order: 7156,
        source: "Int[(g_+h_.*Log[1+e_.*x_])*PolyLog[2,c_.*x_]/x_,x_Symbol] :=
          g \\[Star] Int[PolyLog[2,c*x]/x,x] + h \\[Star] Int[(Log[1+e*x]*PolyLog[2,c*x])/x,x] /;
        FreeQ[{c,e,g,h},x] && EqQ[c+e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(g_) + h__ * (Atom::num(1) + e__ * x_).log()) * (c__ * x_).polylog(2) / x_,
        with: [g_, h__, e__, c__, x_],
        optional: [h__, e__, c__],
        when: { freeq!([c__, e__, g_, h__], x_) && eqq!(&c__ + &e__, 0) },
        rhs: {
            let polylog = (&c__ * x_).polylog(2);
            let log_term = (Atom::num(1) + &e__ * x_).log();
            rubi_star(g_, rubi_rhs_int(&(&polylog / x_), x_)) + rubi_star(h__, rubi_rhs_int(&(log_term * polylog / x_), x_))
        },
    ));
}

fn push_rules_rule_7157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7157,
        source: "Int[x_^m_.*(g_.+h_.*Log[f_.*(d_.+e_.*x_)^n_.])*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          x^(m+1)*(g+h*Log[f*(d+e*x)^n])*PolyLog[2,c*(a+b*x)]/(m+1) +
          b/(m+1) \\[Star] Int[ExpandIntegrand[(g+h*Log[f*(d+e*x)^n])*Log[1-a*c-b*c*x],x^(m+1)/(a+b*x),x],x] -
          e*h*n/(m+1) \\[Star] Int[ExpandIntegrand[PolyLog[2,c*(a+b*x)],x^(m+1)/(d+e*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x] && IntegerQ[m] && NeQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) * (g__ + h__ * (f__ * (d__ + e__ * x_).pow(n_)).log()) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [m_, g__, h__, f__, d__, e__, n_, c__, a__, b__, x_],
        optional: [m_, g__, h__, f__, d__, e__, n_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && integerq!(m_)
                && neq!(m_, -1)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let shifted = &d__ + &e__ * x_;
            let log_factor = &g__ + &h__ * (&f__ * shifted.pow(&n_)).log();
            let argument = &c__ * &affine;
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            let expanded_affine = rubi_expand_integrand_product(
                &(&log_factor * log_argument),
                &(x_.pow(&m_ + 1) / &affine),
                x_,
            );
            let expanded_shifted = rubi_expand_integrand_product(
                &argument.polylog(2),
                &(x_.pow(&m_ + 1) / shifted),
                x_,
            );
            rubi_simp(&(x_.pow(&m_ + 1) * log_factor * argument.polylog(2) / (&m_ + 1)), x_)
                    + rubi_star(b__, rubi_rhs_int(&expanded_affine, x_) / (&m_ + 1))
                    - rubi_star(&e__ * &h__ * &n_ / (&m_ + 1), rubi_rhs_int(&expanded_shifted, x_))
        },
    ));
}

fn push_rules_rule_7158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, px_, x_);
    rules.push(rubi_rule!(
        order: 7158,
        source: "Int[Px_*(g_.+h_.*Log[f_.*(d_.+e_.*x_)^n_.])*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{u=IntHide[Px,x]},
          u*(g+h*Log[f*(d+e*x)^n])*PolyLog[2,c*(a+b*x)] +
          b \\[Star] Int[ExpandIntegrand[(g+h*Log[f*(d+e*x)^n])*Log[1-a*c-b*c*x],u/(a+b*x),x],x] -
          e*h*n \\[Star] Int[ExpandIntegrand[PolyLog[2,c*(a+b*x)],u/(d+e*x),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: Atom::var(px_) * (g__ + h__ * (f__ * (d__ + e__ * x_).pow(n_)).log()) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [px_, g__, h__, f__, d__, e__, n_, c__, a__, b__, x_],
        optional: [g__, h__, f__, d__, e__, n_, c__, a__, b__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_) && poly_q(&px_, x_) },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let shifted = &d__ + &e__ * x_;
            let log_factor = &g__ + &h__ * (&f__ * shifted.pow(&n_)).log();
            let argument = &c__ * &affine;
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            let u = rubi_int_hide(&px_, x_).rubi_rhs();
            let expanded_affine = rubi_expand_integrand_product(&(&log_factor * log_argument), &(&u / &affine), x_);
            let expanded_shifted = rubi_expand_integrand_product(&argument.polylog(2), &(&u / shifted), x_);
            rubi_simp(&(u * log_factor * argument.polylog(2)), x_)
                    + rubi_star(b__, rubi_rhs_int(&expanded_affine, x_))
                    - rubi_star(&e__ * &h__ * &n_, rubi_rhs_int(&expanded_shifted, x_))
        },
    ));
}

fn push_rules_rule_7159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, e__, g__, h__, m_, px_, x_);
    rules.push(rubi_rule!(
        order: 7159,
        source: "Int[x_^m_*Px_*(g_.+h_.*Log[1+e_.*x_])*PolyLog[2,c_.*x_],x_Symbol] :=
          Coeff[Px,x,-m-1] \\[Star] Int[(g+h*Log[1+e*x])*PolyLog[2,c*x]/x,x] +
          Int[x^m*(Px-Coeff[Px,x,-m-1]*x^(-m-1))*(g+h*Log[1+e*x])*PolyLog[2,c*x],x] /;
        FreeQ[{c,e,g,h},x] && PolyQ[Px,x] && ILtQ[m,0] && EqQ[c+e,0] && NeQ[Coeff[Px,x,-m-1],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * Atom::var(px_) * (g__ + h__ * (Atom::num(1) + e__ * x_).log()) * (c__ * x_).polylog(2),
        with: [m_, px_, g__, h__, e__, c__, x_],
        optional: [g__, h__, e__, c__],
        when: {
            freeq!([c__, e__, g__, h__], x_)
                && poly_q(&px_, x_)
                && iltq!(m_, 0)
                && eqq!(&c__ + &e__, 0)
                && integer_i64(&(-&m_ - 1)).is_some_and(|degree| {
                    rubi_coeff(&px_, x_, degree).is_some_and(|coefficient| neq!(coefficient, 0))
                })
        },
        rhs: {
            let degree = integer_i64(&(-&m_ - 1)).rubi_rhs();
            let coefficient = rubi_coeff(&px_, x_, degree).rubi_rhs();
            let log_factor = &g__ + &h__ * (Atom::num(1) + &e__ * x_).log();
            let polylog = (&c__ * x_).polylog(2);
            let first = &coefficient
                * rubi_rhs_int(&(&log_factor * &polylog / x_), x_);
            rubi_star(Atom::num(1), first)
                    + rubi_rhs_int(
                        &(x_.pow(&m_)
                            * (&px_ - coefficient * x_.pow(-&m_ - 1))
                            * log_factor
                            * polylog),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_7160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, px_, x_);
    rules.push(rubi_rule!(
        order: 7160,
        source: "Int[x_^m_.*Px_*(g_.+h_.*Log[f_.*(d_.+e_.*x_)^n_.])*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          With[{u=IntHide[x^m*Px,x]},
          u*(g+h*Log[f*(d+e*x)^n])*PolyLog[2,c*(a+b*x)] +
          b \\[Star] Int[ExpandIntegrand[(g+h*Log[f*(d+e*x)^n])*Log[1-a*c-b*c*x],u/(a+b*x),x],x] -
          e*h*n \\[Star] Int[ExpandIntegrand[PolyLog[2,c*(a+b*x)],u/(d+e*x),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x] && PolyQ[Px,x] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) * Atom::var(px_) * (g__ + h__ * (f__ * (d__ + e__ * x_).pow(n_)).log()) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [m_, px_, g__, h__, f__, d__, e__, n_, c__, a__, b__, x_],
        optional: [m_, g__, h__, f__, d__, e__, n_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && poly_q(&px_, x_)
                && integerq!(m_)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let shifted = &d__ + &e__ * x_;
            let log_factor = &g__ + &h__ * (&f__ * shifted.pow(&n_)).log();
            let argument = &c__ * &affine;
            let log_argument = (Atom::num(1) - &a__ * &c__ - &b__ * &c__ * x_).log();
            let u = rubi_int_hide(&(x_.pow(&m_) * &px_), x_).rubi_rhs();
            let expanded_affine = rubi_expand_integrand_product(&(&log_factor * log_argument), &(&u / &affine), x_);
            let expanded_shifted = rubi_expand_integrand_product(&argument.polylog(2), &(&u / shifted), x_);
            rubi_simp(&(u * log_factor * argument.polylog(2)), x_)
                    + rubi_star(b__, rubi_rhs_int(&expanded_affine, x_))
                    - rubi_star(&e__ * &h__ * &n_, rubi_rhs_int(&expanded_shifted, x_))
        },
    ));
}

fn push_rules_rule_7161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 7161,
        source: "Int[x_^m_*Px_.*(g_.+h_.*Log[f_.*(d_.+e_.*x_)^n_.])*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
          Unintegrable[x^m*Px*(g+h*Log[f*(d+e*x)^n])*PolyLog[2,c*(a+b*x)],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && PolyQ[Px,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: x_.pow(m_) * px__ * (g__ + h__ * (f__ * (d__ + e__ * x_).pow(n_)).log()) * (c__ * (a__ + b__ * x_)).polylog(2),
        with: [m_, px__, g__, h__, f__, d__, e__, n_, c__, a__, b__, x_],
        optional: [px__, g__, h__, f__, d__, e__, n_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && poly_q(&px__, x_)
        },
        rhs: {
            let log_factor = &g__ + &h__ * (&f__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let argument = &c__ * (&a__ + &b__ * x_);
            rubi_unintegrable(x_.pow(&m_) * px__ * log_factor * argument.polylog(2), x_)
        },
    ));
}

fn push_rules_rule_7162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7162,
        source: "Int[PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
          PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) /;
        FreeQ[{F,a,b,c,d,n,p},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * Atom::var(capital_f_).pow(c__ * (a__ + b__ * x_)).pow(p_)).polylog(n_),
        with: [n_, d__, capital_f_, c__, a__, b__, p_, x_],
        optional: [d__, c__, a__, b__, p_],
        when: { freeq!([capital_f_, a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            let exponential = capital_f_

                .pow(&c__ * (&a__ + &b__ * x_))
                .pow(&p_);
            rubi_simp(&((d__ * exponential).polylog(n_ + Atom::num(1))
                    / (&b__ * &c__ * p_ * capital_f_.log())), x_)
        },
    ));
}

fn push_rules_rule_7163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7163,
        source: "Int[(e_.+f_.*x_)^m_.*PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
          (e+f*x)^m*PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) -
          f*m/(b*c*p*Log[F]) \\[Star] Int[(e+f*x)^(m-1)*PolyLog[n+1,d*(F^(c*(a+b*x)))^p],x] /;
        FreeQ[{F,a,b,c,d,e,f,n,p},x] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (d__ * Atom::var(capital_f_).pow(c__ * (a__ + b__ * x_)).pow(p_)).polylog(n_),
        with: [e__, f__, m_, n_, d__, capital_f_, c__, a__, b__, p_, x_],
        optional: [e__, f__, m_, d__, c__, a__, b__, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && gtq!(m_, 0)
        },
        rhs: {
            let affine_power = (&e__ + &f__ * x_).pow(&m_);
            let exponential = capital_f_

                .pow(&c__ * (&a__ + &b__ * x_))
                .pow(&p_);
            let argument = d__ * exponential;
            let denominator = &b__ * &c__ * &p_ * capital_f_.log();
            rubi_simp(&(affine_power * &argument.polylog(&n_ + Atom::num(1)) / &denominator), x_)
                    - rubi_star(&f__ * &m_ / denominator, rubi_rhs_int(&((&e__ + &f__ * x_).pow(m_ - Atom::num(1)) * argument.polylog(n_ + Atom::num(1))), x_))
        },
    ));
}

fn push_rules_rule_7164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__, v_);
    rules.push(rubi_rule!(
        order: 7164,
        source: "Int[u_*PolyLog[n_,v_],x_Symbol] :=
          With[{w=DerivativeDivides[v,u*v,x]},
          w*PolyLog[n+1,v] /;
         Not[FalseQ[w]]] /;
        FreeQ[n,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__ * Atom::var(v_).polylog(n_),
        with: [u__, n_, v_, x_],
        when: {
            freeq!(n_, x_)
                && rubi_derivative_divides(&v_, &(&u__ * &v_), x_).is_some()
        },
        rhs: {
            let v_atom = v_;
            let divisor = rubi_derivative_divides(&v_atom, &(u__ * &v_atom), x_).rubi_rhs();
            rubi_simp(
                &(divisor * v_atom.polylog(n_ + Atom::num(1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_7165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 7165,
        source: "Int[u_*Log[w_]*PolyLog[n_,v_],x_Symbol] :=
          With[{z=DerivativeDivides[v,u*v,x]},
          z*Log[w]*PolyLog[n+1,v] -
          Int[SimplifyIntegrand[z*D[w,x]*PolyLog[n+1,v]/w,x],x] /;
         Not[FalseQ[z]]] /;
        FreeQ[n,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * Atom::var(w_).log() * Atom::var(v_).polylog(n_),
        with: [u__, w_, n_, v_, x_],
        when: {
            freeq!(n_, x_)
                && rubi_inverse_function_free_q(&w_, x_)
                && rubi_derivative_divides(&v_, &(&u__ * &v_), x_).is_some()
        },
        rhs: {
            let v_atom = v_;
            let w_atom = w_;
            let divisor = rubi_derivative_divides(&v_atom, &(u__ * &v_atom), x_).rubi_rhs();
            let first = &divisor
                * w_atom.log()
                * &v_atom.polylog(&n_ + Atom::num(1));
            rubi_simp(&first, x_)
                    - rubi_rhs_int(
                        &rubi_simplify_integrand(
                            &(divisor * rubi_d(&w_atom, x_) * v_atom.polylog(n_ + Atom::num(1)) / w_atom),
                            x_,
                        ),
                        x_,
                    )
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ * (b__ * x_.pow(p_)).pow(q_)).polylog(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (c__ * (a__ + b__ * x_)).polylog(2) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ * (b__ * x_.pow(p_)).pow(q_)).polylog(n_)
}
