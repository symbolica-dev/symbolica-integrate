use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1025(rules);
    let first_rule = rules.len();
    push_rules_rule_1019(rules);
    push_rules_rule_1020(rules);
    push_rules_rule_1021(rules);
    push_rules_rule_1022(rules);
    push_rules_rule_400(rules);
    push_rules_rule_1023(rules);
    push_rules_rule_1024(rules);
    push_rules_rule_404(rules);
    push_rules_rule_1026(rules);
    push_rules_rule_1027(rules);
    push_rules_rule_407(rules);
    push_rules_rule_408(rules);
    push_rules_rule_409(rules);
    push_rules_rule_410(rules);
    push_rules_rule_411(rules);
    push_rules_rule_412(rules);
    push_rules_rule_413(rules);
    push_rules_rule_414(rules);
    push_rules_rule_415(rules);
    push_rules_rule_416(rules);
    push_rules_rule_417(rules);
    push_rules_rule_418(rules);
    push_rules_rule_419(rules);
    push_rules_rule_420(rules);
    push_rules_rule_421(rules);
    push_rules_rule_422(rules);
    push_rules_rule_423(rules);
    push_rules_rule_424(rules);
    push_rules_rule_1028(rules);
    push_rules_rule_1029(rules);
    push_rules_rule_427(rules);
    push_rules_rule_428(rules);
    push_rules_rule_429(rules);
    push_rules_rule_430(rules);
    push_rules_rule_431(rules);
    push_rules_rule_432(rules);
    push_rules_rule_1030(rules);
    push_rules_rule_1031(rules);
    push_rules_rule_1032(rules);
    push_rules_rule_1033(rules);
    push_rules_rule_1034(rules);
    push_rules_rule_1035(rules);
    push_rules_rule_1036(rules);
    push_rules_rule_2040(rules);
    push_rules_rule_2041(rules);
    // Every loaded DownValue in this interval has three binomial factors with
    // the same monomial exponent n. This is a necessary source-pattern bound.
    for rule in &mut rules[first_rule..] {
        if rule
            .downvalue_order
            .is_some_and(|order| (1019..=1032).contains(&order))
        {
            rule.required_common_binomial_exponent_factor_count = 3;
        }
        if rule
            .downvalue_order
            .is_some_and(|order| (1034..=1036).contains(&order))
        {
            rule.require_negated_binomial_exponent_pair = true;
        }
    }
}

fn push_rules_rule_1019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    let rule = rubi_rule!(
        order: 1019,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[p,0] && IGtQ[q,0] && IGtQ[r,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    );
    rules.push(
        rule.with_common_positive_integer_binomial_factor_count(3)
            .with_early_numeric_bound(p_, RubiEarlyNumericBound::IntegerGreaterThan(0))
            .with_early_numeric_bound(q_, RubiEarlyNumericBound::IntegerGreaterThan(0))
            .with_early_numeric_bound(r_, RubiEarlyNumericBound::IntegerGreaterThan(0)),
    );
}

fn push_rules_rule_1020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 1020,
        source: "Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[1/(a+b*x^n),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[1/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(n_)) / ((a__ + b__ * x_.pow(n_)) * (c__ + d__ * x_.pow(n_))),
        with: [a__, b__, c__, d__, e__, f__, n_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_], x_) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_integrand = Atom::num(1) / (&a__ + &b__ * x_.pow(&n_));
            let second_integrand = Atom::num(1) / (&c__ + &d__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star((&b__ * &e__ - &a__ * &f__) / &det, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / det, second)
        },
    ));
}

fn push_rules_rule_1021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 1021,
        source: "Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
          f/b \\[Star] Int[1/Sqrt[c+d*x^n],x] +
          (b*e-a*f)/b \\[Star] Int[1/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
        FreeQ[{a,b,c,d,e,f,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(n_)) / ((a__ + b__ * x_.pow(n_)) * (c__ + d__ * x_.pow(n_)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, n_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = Atom::num(1) / second_base.sqrt();
            let second_integrand = Atom::num(1) / (first_base * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&f__ / &b__, first)
                    + rubi_star((&b__ * &e__ - &a__ * &f__) / &b__, second)
        },
    ));
}

fn push_rules_rule_1022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 1022,
        source: "Int[(e_+f_.*x_^n_)/(Sqrt[a_+b_.*x_^n_]*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
          f/b \\[Star] Int[Sqrt[a+b*x^n]/Sqrt[c+d*x^n],x] +
          (b*e-a*f)/b \\[Star] Int[1/(Sqrt[a+b*x^n]*Sqrt[c+d*x^n]),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] &&
          Not[EqQ[n,2] && (PosQ[b/a] && PosQ[d/c] || NegQ[b/a] && (PosQ[d/c] || GtQ[a,0] && (Not[GtQ[c,0]] || SimplerSqrtQ[-b/a,-d/c])))]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(n_))
            / ((a__ + b__ * x_.pow(n_)).sqrt() * (c__ + d__ * x_.pow(n_)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, n_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && !(eqq!(n_, 2)
                    && ((posq!(&b__ / &a__) && posq!(&d__ / &c__))
                        || (negq!(&b__ / &a__)
                            && (posq!(&d__ / &c__)
                                || (gtq!(a__, 0)
                                    && (!gtq!(c__, 0)
                                        || rubi_simpler_sqrt_q(&(-&b__ / &a__), &(-&d__ / &c__))))))))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = first_base.sqrt() / second_base.sqrt();
            let second_integrand = Atom::num(1) / (first_base.sqrt() * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&f__ / &b__, first)
                    + rubi_star((&b__ * &e__ - &a__ * &f__) / &b__, second)
        },
    ));
}

fn push_rules_rule_400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 400,
        source: "Int[(e_+f_.*x_^2)/(Sqrt[a_+b_.*x_^2]*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[Sqrt[a+b*x^2]/(c+d*x^2)^(3/2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[b/a] && PosQ[d/c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2))
            / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).pow((3, 2))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && posq!(&b__ / &a__)
                && posq!(&d__ / &c__)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first_integrand = Atom::num(1) / (first_base.sqrt() * second_base.sqrt());
            let second_integrand = first_base.sqrt() / second_base.pow((3, 2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star((&b__ * &e__ - &a__ * &f__) / &det, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / det, second)
        },
    ));
}

fn push_rules_rule_1023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 1023,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*n*(p+1)) +
          1/(a*b*n*(p+1)) \\[Star]
            Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(b*e*n*(p+1)+b*e-a*f)+d*(b*e*n*(p+1)+(b*e-a*f)*(n*q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Binomial product recurrence 1 with p=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, x_],
        optional: [b__, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &a__ * &b__ * &n_ * (&p_ + Atom::num(1));
            let direct = -&be_af * x_ * first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_) / &denominator;
            let simp = rubi_simp(
                &(&c__ * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1)) + &be_af)
                    + &d__
                        * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1))
                            + &be_af * (&n_ * &q_ + Atom::num(1)))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_ - Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(rule.with_common_positive_integer_binomial_factor_count(2));
}

fn push_rules_rule_1024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1024,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(b*c-a*d)*(p+1)) +
          1/(a*n*(b*c-a*d)*(p+1)) \\[Star]
            Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*(b*e-a*f)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,q},x] && LtQ[p,-1]",
        desc: "Binomial product recurrence 2a with p=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, x_],
        optional: [b__, d__, f__, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_, q_], x_) && ltq!(p_, -1) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let det = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &a__ * &n_ * &det * (&p_ + Atom::num(1));
            let direct = -&be_af
                * x_
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / &denominator;
            let simp = rubi_simp(
                &(&c__ * &be_af
                    + &e__ * &n_ * &det * (&p_ + Atom::num(1))
                    + &d__
                        * &be_af
                        * (&n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 1025,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          f*x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*(n*(p+q+1)+1)) +
          1/(b*(n*(p+q+1)+1)) \\[Star]
            Int[(a+b*x^n)^p*(c+d*x^n)^(q-1)*Simp[c*(b*e-a*f+b*e*n*(p+q+1))+(d*(b*e-a*f)+f*n*q*(b*c-a*d)+b*d*e*n*(p+q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && GtQ[q,0] && NeQ[n*(p+q+1)+1,0]",
        desc: "Binomial product recurrence 3a with p=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, x_],
        optional: [b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && gtq!(q_, 0)
                && neq!(&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let det = &b__ * &c__ - &a__ * &d__;
            let denominator = &b__ * (&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1));
            let direct = rubi_simp(
                &(&f__
                    * x_
                    * first_base.pow(&p_ + Atom::num(1))
                    * second_base.pow(&q_)
                    / &denominator),
                x_,
            );
            let simp = rubi_simp(
                &(&c__ * (&be_af + &b__ * &e__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                    + (&d__ * &be_af
                        + &f__ * &n_ * &q_ * &det
                        + &b__ * &d__ * &e__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = first_base.pow(&p_) * second_base.pow(&q_ - Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    );
    rules.push(
        rule.with_common_binomial_exponent_factor_count(3)
            .with_common_positive_integer_binomial_factor_count(2),
    );
}

fn push_rules_rule_404(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 404,
        source: "Int[(e_+f_.*x_^4)/((a_+b_.*x_^4)^(3/4)*(c_+d_.*x_^4)),x_Symbol] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[1/(a+b*x^4)^(3/4),x] - (d*e-c*f)/(b*c-a*d) \\[Star] Int[(a+b*x^4)^(1/4)/(c+d*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(4)) / ((a__ + b__ * x_.pow(4)).pow((3, 4)) * (c__ + d__ * x_.pow(4))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(4);
            let second_base = &c__ + &d__ * x_.pow(4);
            let first_integrand = Atom::num(1) / first_base.pow((3, 4));
            let second_integrand = first_base.pow((1, 4)) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star((&b__ * &e__ - &a__ * &f__) / &det, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / det, second)
        },
    ));
}

fn push_rules_rule_1026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1026,
        source: "Int[(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
          f/d \\[Star] Int[(a+b*x^n)^p,x] + (d*e-c*f)/d \\[Star] Int[(a+b*x^n)^p/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,p,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(n_)).pow(p_) * (e__ + f__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_)),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_, n_], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = first_base.pow(&p_);
            let second_integrand = first_base.pow(&p_) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&f__ / &d__, first)
                    + rubi_star((&d__ * &e__ - &c__ * &f__) / &d__, second)
        },
    ));
}

fn push_rules_rule_1027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1027,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          e \\[Star] Int[(a+b*x^n)^p*(c+d*x^n)^q,x] + f \\[Star] Int[x^n*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,f,n,p,q},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, x_],
        optional: [b__, d__, f__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = first_base.pow(&p_) * second_base.pow(&q_);
            let second_integrand = x_.pow(&n_) * first_base.pow(&p_) * second_base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__, first) + rubi_star(f__, second)
        },
    ));
}

fn push_rules_rule_407(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 407,
        source: "Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/((a+b*x^2)*Sqrt[e+f*x^2]),x] -
          d/(b*c-a*d) \\[Star] Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2)) * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_integrand =
                Atom::num(1) / ((&a__ + &b__ * x_.pow(2)) * (&e__ + &f__ * x_.pow(2)).sqrt());
            let second_integrand =
                Atom::num(1) / ((&c__ + &d__ * x_.pow(2)) * (&e__ + &f__ * x_.pow(2)).sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&b__ / &det, first)
                    - rubi_star(&d__ / det, second)
        },
    ));
}

fn push_rules_rule_408(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 408,
        source: "Int[1/(x_^2*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          1/c \\[Star] Int[1/(x^2*Sqrt[e+f*x^2]),x] -
          d/c \\[Star] Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
        FreeQ[{c,d,e,f},x] && NeQ[d*e-c*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / (x_.pow(2) * (c__ + d__ * x_.pow(2)) * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [c__, d__, e__, f__, x_],
        optional: [d__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let first_integrand = Atom::num(1) / (x_.pow(2) * (&e__ + &f__ * x_.pow(2)).sqrt());
            let second_integrand =
                Atom::num(1) / ((&c__ + &d__ * x_.pow(2)) * (&e__ + &f__ * x_.pow(2)).sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &c__, first)
                    - rubi_star(&d__ / &c__, second)
        },
    ));
}

fn push_rules_rule_409(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 409,
        source: "Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
          d/b \\[Star] Int[Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] + (b*c-a*d)/b \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[d/c,0] && GtQ[f/e,0] && Not[SimplerSqrtQ[d/c,f/e]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(&d__ / &c__, 0)
                && gtq!(&f__ / &e__, 0)
                && !rubi_simpler_sqrt_q(&(&d__ / &c__), &(&f__ / &e__))
        },
        rhs: {
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.sqrt() / first_base.sqrt();
            let second_integrand =
                second_base.sqrt() / ((&a__ + &b__ * x_.pow(2)) * first_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_410(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 410,
        source: "Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
          d/b \\[Star] Int[Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] + (b*c-a*d)/b \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[SimplerSqrtQ[-f/e,-d/c]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !rubi_simpler_sqrt_q(&(-&f__ / &e__), &(-&d__ / &c__))
        },
        rhs: {
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.sqrt() / first_base.sqrt();
            let second_integrand =
                second_base.sqrt() / ((&a__ + &b__ * x_.pow(2)) * first_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_411(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 411,
        source: "Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          -f/(b*e-a*f) \\[Star] Int[1/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] +
          b/(b*e-a*f) \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && GtQ[d/c,0] && GtQ[f/e,0] && Not[SimplerSqrtQ[d/c,f/e]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && gtq!(&d__ / &c__, 0)
                && gtq!(&f__ / &e__, 0)
                && !rubi_simpler_sqrt_q(&(&d__ / &c__), &(&f__ / &e__))
        },
        rhs: {
            let denominator = &b__ * &e__ - &a__ * &f__;
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = Atom::num(1) / (first_base.sqrt() * second_base.sqrt());
            let second_integrand =
                second_base.sqrt() / ((&a__ + &b__ * x_.pow(2)) * first_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&f__ / &denominator, first)
                    + rubi_star(&b__ / denominator, second)
        },
    ));
}

fn push_rules_rule_412(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 412,
        source: "Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          1/(a*Sqrt[c]*Sqrt[e]*Rt[-d/c,2])*EllipticPi[b*c/(a*d), ArcSin[Rt[-d/c,2]*x], c*f/(d*e)] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[d/c,0]] && GtQ[c,0] && GtQ[e,0] && Not[Not[GtQ[f/e,0]] && SimplerSqrtQ[-f/e,-d/c]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !gtq!(&d__ / &c__, 0)
                && gtq!(c__, 0)
                && gtq!(e__, 0)
                && !(!gtq!(&f__ / &e__, 0) && rubi_simpler_sqrt_q(&(-&f__ / &e__), &(-&d__ / &c__)))
        },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            rubi_simp(&(rubi_elliptic_pi(
                    &b__ * &c__ / (&a__ * &d__),
                    (&rt * x_).asin(),
                    &c__ * &f__ / (&d__ * &e__),
                ) / (&a__ * c__.sqrt() * e__.sqrt() * rt)), x_)
        },
    ));
}

fn push_rules_rule_413(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 413,
        source: "Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2] \\[Star] Int[1/((a+b*x^2)*Sqrt[1+d/c*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && !gtq!(c__, 0) },
        rhs: {
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            let normalized = Atom::num(1) + &d__ * x_.pow(2) / &c__;
            let recursive_integrand =
                Atom::num(1) / ((&a__ + &b__ * x_.pow(2)) * normalized.sqrt() * second_base.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(normalized.sqrt() / first_base.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_414(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 414,
        source: "Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          c*Sqrt[e+f*x^2]/(a*e*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(e+f*x^2)/(e*(c+d*x^2))])*
            EllipticPi[1-b*c/(a*d),ArcTan[Rt[d/c,2]*x],1-c*f/(d*e)] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && posq!(&d__ / &c__) },
        rhs: {
            let rt = rubi_rt(&(&d__ / &c__), 2);
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            rubi_simp(&(&c__ * second_base.sqrt()
                    * rubi_elliptic_pi(
                        Atom::num(1) - &b__ * &c__ / (&a__ * &d__),
                        (&rt * x_).atan(),
                        Atom::num(1) - &c__ * &f__ / (&d__ * &e__),
                    ) / (&a__
                    * &e__
                    * rt
                    * first_base.sqrt()
                    * (&c__ * second_base / (&e__ * first_base)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_415(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 415,
        source: "Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          d/b \\[Star] Int[1/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] +
          (b*c-a*d)/b \\[Star] Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NegQ[d/c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && negq!(&d__ / &c__) },
        rhs: {
            let first_base = &c__ + &d__ * x_.pow(2);
            let second_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = Atom::num(1) / (first_base.sqrt() * second_base.sqrt());
            let second_integrand =
                Atom::num(1) / ((&a__ + &b__ * x_.pow(2)) * first_base.sqrt() * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_416(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 416,
        source: "Int[Sqrt[e_+f_.*x_^2]/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] -
          d/(b*c-a*d) \\[Star] Int[Sqrt[e+f*x^2]/(c+d*x^2)^(3/2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2)).sqrt()
            / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2)).pow((3, 2))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && posq!(&d__ / &c__)
                && posq!(&f__ / &e__)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = third_base.sqrt() / (first_base * second_base.sqrt());
            let second_integrand = third_base.sqrt() / second_base.pow((3, 2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&b__ / &det, first)
                    - rubi_star(&d__ / det, second)
        },
    ));
}

fn push_rules_rule_417(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 417,
        source: "Int[(e_+f_.*x_^2)^(3/2)/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[Sqrt[e+f*x^2]/(c+d*x^2)^(3/2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2)).pow((3, 2))
            / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2)).pow((3, 2))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && posq!(&d__ / &c__)
                && posq!(&f__ / &e__)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = third_base.sqrt() / (first_base * second_base.sqrt());
            let second_integrand = third_base.sqrt() / second_base.pow((3, 2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star((&b__ * &e__ - &a__ * &f__) / &det, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / det, second)
        },
    ));
}

fn push_rules_rule_418(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 418,
        source: "Int[(c_+d_.*x_^2)^(3/2)*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
          (b*c-a*d)^2/b^2 \\[Star] Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] +
          d/b^2 \\[Star] Int[(2*b*c-a*d+b*d*x^2)*Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).pow((3, 2)) * (e__ + f__ * x_.pow(2)).sqrt()
            / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && posq!(&d__ / &c__)
                && posq!(&f__ / &e__)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = third_base.sqrt() / (first_base * second_base.sqrt());
            let second_integrand =
                (Atom::num(2) * &b__ * &c__ - &a__ * &d__ + &b__ * &d__ * x_.pow(2)) * third_base.sqrt()
                    / second_base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(det.pow(2) / b__.pow(2), first)
                    + rubi_star(&d__ / b__.pow(2), second)
        },
    ));
}

fn push_rules_rule_419(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 419,
        source: "Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
          b*(b*e-a*f)/(b*c-a*d)^2 \\[Star] Int[(c+d*x^2)^(q+2)*(e+f*x^2)^(r-1)/(a+b*x^2),x] -
          1/(b*c-a*d)^2 \\[Star] Int[(c+d*x^2)^q*(e+f*x^2)^(r-1)*(2*b*c*d*e-a*d^2*e-b*c^2*f+d^2*(b*e-a*f)*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && LtQ[q,-1] && GtQ[r,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, q_, r_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && ltq!(q_, -1)
                && gtq!(r_, 1)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand =
                second_base.pow(&q_ + Atom::num(2)) * third_base.pow(&r_ - Atom::num(1)) / first_base;
            let second_integrand = second_base.pow(&q_)
                * third_base.pow(&r_ - Atom::num(1))
                * (Atom::num(2) * &b__ * &c__ * &d__ * &e__ - &a__ * d__.pow(2) * &e__ - &b__ * c__.pow(2) * &f__
                    + d__.pow(2) * (&b__ * &e__ - &a__ * &f__) * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&b__ * (&b__ * &e__ - &a__ * &f__) / det.pow(2), first) - rubi_star(Atom::num(1) / det.pow(2), second)
        },
    ));
}

fn push_rules_rule_420(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 420,
        source: "Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
          d/b \\[Star] Int[(c+d*x^2)^(q-1)*(e+f*x^2)^r,x] +
          (b*c-a*d)/b \\[Star] Int[(c+d*x^2)^(q-1)*(e+f*x^2)^r/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,r},x] && GtQ[q,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, q_, r_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, r_], x_) && gtq!(q_, 1) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.pow(&q_ - Atom::num(1)) * third_base.pow(&r_);
            let second_integrand = second_base.pow(&q_ - Atom::num(1)) * third_base.pow(&r_) / first_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_421(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 421,
        source: "Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
          b^2/(b*c-a*d)^2 \\[Star] Int[(c+d*x^2)^(q+2)*(e+f*x^2)^r/(a+b*x^2),x] -
          d/(b*c-a*d)^2 \\[Star] Int[(c+d*x^2)^q*(e+f*x^2)^r*(2*b*c-a*d+b*d*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,r},x] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, q_, r_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, r_], x_) && ltq!(q_, -1) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.pow(&q_ + Atom::num(2)) * third_base.pow(&r_) / first_base;
            let second_integrand = second_base.pow(&q_)
                * third_base.pow(&r_)
                * (Atom::num(2) * &b__ * &c__ - &a__ * &d__ + &b__ * &d__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(b__.pow(2) / det.pow(2), first)
                    - rubi_star(&d__ / det.pow(2), second)
        },
    ));
}

fn push_rules_rule_422(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 422,
        source: "Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
          -d/(b*c-a*d) \\[Star] Int[(c+d*x^2)^q*(e+f*x^2)^r,x] +
          b/(b*c-a*d) \\[Star] Int[(c+d*x^2)^(q+1)*(e+f*x^2)^r/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,r},x] && LeQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, q_, r_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, r_], x_) && leq!(q_, -1) },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.pow(&q_) * third_base.pow(&r_);
            let second_integrand = second_base.pow(&q_ + Atom::num(1)) * third_base.pow(&r_) / first_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&d__ / &det, first)
                    + rubi_star(&b__ / det, second)
        },
    ));
}

fn push_rules_rule_423(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 423,
        source: "Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2)^2,x_Symbol] :=
          x*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]/(2*a*(a+b*x^2)) +
          d*f/(2*a*b^2) \\[Star] Int[(a-b*x^2)/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] +
          (b^2*c*e-a^2*d*f)/(2*a*b^2) \\[Star] Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sqrt() * (e__ + f__ * x_.pow(2)).sqrt()
            / (a__ + b__ * x_.pow(2)).pow(2),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let direct = x_ * second_base.sqrt() * third_base.sqrt() / (Atom::num(2) * &a__ * &first_base);
            let first_integrand =
                (&a__ - &b__ * x_.pow(2)) / (second_base.sqrt() * third_base.sqrt());
            let second_integrand = Atom::num(1) / (first_base * second_base.sqrt() * third_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(&d__ * &f__ / (Atom::num(2) * &a__ * b__.pow(2)), first)
                    + rubi_star((b__.pow(2) * &c__ * &e__ - a__.pow(2) * &d__ * &f__)
                            / (Atom::num(2) * &a__ * b__.pow(2)), second)
        },
    ));
}

fn push_rules_rule_424(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 424,
        source: "Int[1/((a_+b_.*x_^2)^2*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          b^2*x*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]/(2*a*(b*c-a*d)*(b*e-a*f)*(a+b*x^2)) -
          d*f/(2*a*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x^2)/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] +
          (b^2*c*e+3*a^2*d*f-2*a*b*(d*e+c*f))/(2*a*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_.pow(2)).pow(2)
                * (c__ + d__ * x_.pow(2)).sqrt()
                * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let det_c = &b__ * &c__ - &a__ * &d__;
            let det_e = &b__ * &e__ - &a__ * &f__;
            let direct = b__.pow(2) * x_ * second_base.sqrt() * third_base.sqrt()
                / (Atom::num(2) * &a__ * &det_c * &det_e * &first_base);
            let first_integrand = first_base / (second_base.sqrt() * third_base.sqrt());
            let second_integrand =
                Atom::num(1) / ((&a__ + &b__ * x_.pow(2)) * second_base.sqrt() * third_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(&d__ * &f__ / (Atom::num(2) * &a__ * &det_c * &det_e), first)
                    + rubi_star((b__.pow(2) * &c__ * &e__
                            + Atom::num(3) * a__.pow(2) * &d__ * &f__
                            - Atom::num(2) * &a__ * &b__ * (&d__ * &e__ + &c__ * &f__))
                            / (Atom::num(2) * &a__ * det_c * det_e), second)
        },
    ));
}

fn push_rules_rule_1028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1028,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
          d/b \\[Star] Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*(e+f*x^n)^r,x] +
          (b*c-a*d)/b \\[Star] Int[(a+b*x^n)^p*(c+d*x^n)^(q-1)*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,n,r},x] && ILtQ[p,0] && GtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, r_], x_)
                && iltq!(p_, 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let third_base = &e__ + &f__ * x_.pow(&n_);
            let first_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_ - Atom::num(1)) * third_base.pow(&r_);
            let second_integrand =
                first_base.pow(&p_) * second_base.pow(&q_ - Atom::num(1)) * third_base.pow(&r_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_1029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1029,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(a+b*x^n)^p*(c+d*x^n)^(q+1)*(e+f*x^n)^r,x] -
          d/(b*c-a*d) \\[Star] Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,n,q},x] && ILtQ[p,0] && LeQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, q_], x_)
                && iltq!(p_, 0)
                && leq!(q_, -1)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let third_base = &e__ + &f__ * x_.pow(&n_);
            let first_integrand =
                first_base.pow(&p_) * second_base.pow(&q_ + Atom::num(1)) * third_base.pow(&r_);
            let second_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_) * third_base.pow(&r_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&b__ / &det, first)
                    - rubi_star(&d__ / det, second)
        },
    ));
}

fn push_rules_rule_427(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 427,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(c*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))]) \\[Star]
            Subst[Int[1/(Sqrt[1-(b*c-a*d)*x^2/c]*Sqrt[1-(b*e-a*f)*x^2/e]),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_.pow(2)).sqrt()
                * (c__ + d__ * x_.pow(2)).sqrt()
                * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let prefactor = second_base.sqrt() * (&a__ * &third_base / (&e__ * &first_base)).sqrt()
                / (&c__ * third_base.sqrt() * (&a__ * &second_base / (&c__ * &first_base)).sqrt());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / ((Atom::num(1) - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(2) / &c__).sqrt()
                    * (Atom::num(1) - (&b__ * &e__ - &a__ * &f__) * sub_atom.pow(2) / &e__).sqrt());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = x_ / first_base.sqrt();
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(prefactor, substituted)
        },
    ));
}

fn push_rules_rule_428(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 428,
        source: "Int[Sqrt[a_+b_.*x_^2]/(Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          a*Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(c*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))]) \\[Star]
            Subst[Int[1/((1-b*x^2)*Sqrt[1-(b*c-a*d)*x^2/c]*Sqrt[1-(b*e-a*f)*x^2/e]),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).sqrt()
            / ((c__ + d__ * x_.pow(2)).sqrt() * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let prefactor = &a__ * second_base.sqrt() * (&a__ * &third_base / (&e__ * &first_base)).sqrt()
                / (&c__ * third_base.sqrt() * (&a__ * &second_base / (&c__ * &first_base)).sqrt());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / ((Atom::num(1) - &b__ * sub_atom.pow(2))
                    * (Atom::num(1) - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(2) / &c__).sqrt()
                    * (Atom::num(1) - (&b__ * &e__ - &a__ * &f__) * sub_atom.pow(2) / &e__).sqrt());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = x_ / first_base.sqrt();
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(prefactor, substituted)
        },
    ));
}

fn push_rules_rule_429(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 429,
        source: "Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)^(3/2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(a*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))]) \\[Star]
            Subst[Int[Sqrt[1-(b*c-a*d)*x^2/c]/Sqrt[1-(b*e-a*f)*x^2/e],x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sqrt()
            / ((a__ + b__ * x_.pow(2)).pow((3, 2)) * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let prefactor = second_base.sqrt() * (&a__ * &third_base / (&e__ * &first_base)).sqrt()
                / (&a__ * third_base.sqrt() * (&a__ * &second_base / (&c__ * &first_base)).sqrt());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (Atom::num(1) - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(2) / &c__).sqrt()
                    / (Atom::num(1) - (&b__ * &e__ - &a__ * &f__) * sub_atom.pow(2) / &e__).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = x_ / first_base.sqrt();
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(prefactor, substituted)
        },
    ));
}

fn push_rules_rule_430(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 430,
        source: "Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/Sqrt[e_+f_.*x_^2],x_Symbol] :=
          d*x*Sqrt[a+b*x^2]*Sqrt[e+f*x^2]/(2*f*Sqrt[c+d*x^2]) -
          c*(d*e-c*f)/(2*f) \\[Star] Int[Sqrt[a+b*x^2]/((c+d*x^2)^(3/2)*Sqrt[e+f*x^2]),x] +
          b*c*(d*e-c*f)/(2*d*f) \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] -
          (b*d*e-b*c*f-a*d*f)/(2*d*f) \\[Star] Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[(d*e-c*f)/c]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && posq!((&d__ * &e__ - &c__ * &f__) / &c__)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let balance = &d__ * &e__ - &c__ * &f__;
            let direct = &d__ * x_ * first_base.sqrt() * third_base.sqrt()
                / (Atom::num(2) * &f__ * second_base.sqrt());
            let first_integrand = first_base.sqrt() / (second_base.pow((3, 2)) * third_base.sqrt());
            let second_integrand =
                Atom::num(1) / (first_base.sqrt() * second_base.sqrt() * third_base.sqrt());
            let third_integrand = second_base.sqrt() / (first_base.sqrt() * third_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(&c__ * &balance / (Atom::num(2) * &f__), first)
                    + rubi_star(&b__ * &c__ * &balance / (Atom::num(2) * &d__ * &f__), second)
                    - rubi_star((&b__ * &d__ * &e__ - &b__ * &c__ * &f__ - &a__ * &d__ * &f__)
                            / (Atom::num(2) * &d__ * f__), third)
        },
    ));
}

fn push_rules_rule_431(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 431,
        source: "Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/Sqrt[e_+f_.*x_^2],x_Symbol] :=
          x*Sqrt[a+b*x^2]*Sqrt[c+d*x^2]/(2*Sqrt[e+f*x^2]) +
          e*(b*e-a*f)/(2*f) \\[Star] Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*(e+f*x^2)^(3/2)),x] +
          (b*e-a*f)*(d*e-2*c*f)/(2*f^2) \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] -
          (b*d*e-b*c*f-a*d*f)/(2*f^2) \\[Star] Int[Sqrt[e+f*x^2]/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NegQ[(d*e-c*f)/c]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && negq!((&d__ * &e__ - &c__ * &f__) / &c__)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let mixed = &b__ * &d__ * &e__ - &b__ * &c__ * &f__ - &a__ * &d__ * &f__;
            let direct = x_ * first_base.sqrt() * second_base.sqrt() / (Atom::num(2) * third_base.sqrt());
            let first_integrand = second_base.sqrt() / (first_base.sqrt() * third_base.pow((3, 2)));
            let second_integrand =
                Atom::num(1) / (first_base.sqrt() * second_base.sqrt() * third_base.sqrt());
            let third_integrand = third_base.sqrt() / (first_base.sqrt() * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(&e__ * &be_af / (Atom::num(2) * &f__), first)
                    + rubi_star(&be_af * (&d__ * &e__ - Atom::num(2) * &c__ * &f__)
                            / (Atom::num(2) * f__.pow(2)), second)
                    - rubi_star(&mixed / (Atom::num(2) * f__.pow(2)), third)
        },
    ));
}

fn push_rules_rule_432(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 432,
        source: "Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/(e_+f_.*x_^2)^(3/2),x_Symbol] :=
          b/f \\[Star] Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*Sqrt[e+f*x^2]),x] -
          (b*e-a*f)/f \\[Star] Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*(e+f*x^2)^(3/2)),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).sqrt()
            / (e__ + f__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first_integrand = second_base.sqrt() / (first_base.sqrt() * third_base.sqrt());
            let second_integrand = second_base.sqrt() / (first_base.sqrt() * third_base.pow((3, 2)));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&b__ / &f__, first)
                    - rubi_star((&b__ * &e__ - &a__ * &f__) / f__, second)
        },
    ));
}

fn push_rules_rule_1030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1030,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_) && igtq!(n_, 0) },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let u = rubi_expand_integrand(&integrand, x_);
            if !rubi_sum_q(&u) {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_1031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1031,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && ILtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_) && iltq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(-&n_)).pow(&r_)
                / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(
                &transformed,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_1032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1032,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          Unintegrable[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_, r_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                    * (&e__ + &f__ * x_.pow(&n_)).pow(&r_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, p_, q_, r_, u_, v_, w_);
    let rule = rubi_rule!(
        order: 1033,
        source: "Int[(a_.+b_.*u_^n_)^p_.*(c_.+d_.*v_^n_)^q_.*(e_.+f_.*w_^n_)^r_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,p,n,q,r},x] && EqQ[u,v] && EqQ[u,w] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u_.pow(n_)).pow(p_)
            * (c__ + d__ * v_.pow(n_)).pow(q_)
            * (e__ + f__ * w_.pow(n_)).pow(r_),
        with: [a__, b__, c__, d__, e__, f__, u_, v_, w_, n_, p_, q_, r_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_, q_, r_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_],
        x_linear: [u_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, n_, q_, r_], x_)
                && eqq!(u_, v_)
                && eqq!(u_, w_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let slope = rubi_coefficient(&u_, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&n_)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &u_);

            rubi_star(Atom::num(1) / slope, substituted)
        },
    );
    rules.push(rule.with_common_polynomial_base_degree_count(3));
}

fn push_rules_rule_1034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1034,
        source: "Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          Int[(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r/x^(n*q),x] /;
        FreeQ[{a,b,c,d,e,f,n,p,r},x] && EqQ[mn,-n] && IntegerQ[q]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, mn_, p_, q_, r_, x_],
        optional: [a__, b__, d__, f__, n_, mn_, p_, r_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, r_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(q_)
        },
        rhs: {
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_)
                / x_.pow(&n_ * &q_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1035,
        source: "Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          Int[x^(n*(p+r))*(b+a*x^(-n))^p*(c+d*x^(-n))^q*(f+e*x^(-n))^r,x] /;
        FreeQ[{a,b,c,d,e,f,n,q},x] && EqQ[mn,-n] && IntegerQ[p] && IntegerQ[r]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, mn_, p_, q_, r_, x_],
        optional: [a__, b__, d__, f__, n_, mn_, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, q_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
                && integerq!(r_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&n_ * (&p_ + &r_))
                * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&f__ + &e__ * x_.pow(-&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1036,
        source: "Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q] \\[Star] Int[(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r/x^(n*q),x] /;
        FreeQ[{a,b,c,d,e,f,n,p,q,r},x] && EqQ[mn,-n] && Not[IntegerQ[q]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, mn_, p_, q_, r_, x_],
        optional: [a__, b__, d__, f__, n_, mn_, p_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_, r_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(q_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_)
                / x_.pow(&n_ * &q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&n_ * &frac_q) * (&c__ + &d__ * x_.pow(-&n_)).pow(&frac_q) / (&d__ + &c__ * x_.pow(&n_)).pow(frac_q), recursive)
        },
    ));
}

fn push_rules_rule_2040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, e1__, e2__, f1__, f2__, n_, n2_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2040,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
          Int[(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e1,f1,e2,f2,n,p,q,r},x] && EqQ[n2,n/2] && EqQ[e2*f1+e1*f2,0] && (IntegerQ[r] || GtQ[e1,0] && GtQ[e2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e1__, f1__, e2__, f2__, n_, n2_, p_, q_, r_, x_],
        optional: [b__, d__, f1__, f2__, n2_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e1__, f1__, e2__, f2__, n_, p_, q_, r_], x_)
                && eqq!(n2_, &n_ / Atom::num(2))
                && eqq!(&e2__ * &f1__ + &e1__ * &f2__, 0)
                && (integerq!(r_) || gtq!(e1__, 0) && gtq!(e2__, 0))
        },
        rhs: {
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, e1__, e2__, f1__, f2__, n_, n2_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2041,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
          (e1+f1*x^(n/2))^FracPart[r]*(e2+f2*x^(n/2))^FracPart[r]/(e1*e2+f1*f2*x^n)^FracPart[r] \\[Star]
            Int[(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e1,f1,e2,f2,n,p,q,r},x] && EqQ[n2,n/2] && EqQ[e2*f1+e1*f2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e1__, f1__, e2__, f2__, n_, n2_, p_, q_, r_, x_],
        optional: [b__, d__, f1__, f2__, n2_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e1__, f1__, e2__, f2__, n_, p_, q_, r_], x_)
                && eqq!(n2_, &n_ / Atom::num(2))
                && eqq!(&e2__ * &f1__ + &e1__ * &f2__, 0)
        },
        rhs: {
            let frac_r = rubi_frac_part(&r_);
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&e1__ + &f1__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_r) * (&e2__ + &f2__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_r) / (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(frac_r), recursive)
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
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).sqrt() / (e__ + f__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(mn_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f1__ = symbols.f1__;
    let f2__ = symbols.f2__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e1__ + f1__ * x_.pow(n2_)).pow(r_)
        * (e2__ + f2__ * x_.pow(n2_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_) * (e__ + f__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
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
    (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(2)).pow(q_) * (e__ + f__ * x_.pow(2)).pow(r_) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(2)).sqrt() * (e__ + f__ * x_.pow(2)).sqrt() / (a__ + b__ * x_.pow(2))
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
    (c__ + d__ * x_.pow(2)).sqrt() / ((a__ + b__ * x_.pow(2)) * (e__ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((a__ + b__ * x_.pow(2))
            * (c__ + d__ * x_.pow(2)).sqrt()
            * (e__ + f__ * x_.pow(2)).sqrt())
}
