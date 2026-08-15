use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_396(rules);
    push_rules_rule_397(rules);
    push_rules_rule_398(rules);
    push_rules_rule_399(rules);
    push_rules_rule_401(rules);
    push_rules_rule_402(rules);
    push_rules_rule_403(rules);
    push_rules_rule_405(rules);
    push_rules_rule_406(rules);
    push_rules_rule_425(rules);
    push_rules_rule_426(rules);
    push_rules_rule_433(rules);
    push_rules_rule_434(rules);
}

fn push_rules_rule_396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, x_);
    let rule = rubi_rule!(
        order: 396,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2)^r_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IGtQ[r,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, r_, x_],
        optional: [b__, d__, f__, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                * (&e__ + &f__ * x_.pow(2)).pow(&r_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 397,
        source: "Int[(e_+f_.*x_^2)/((a_+b_.*x_^2)*(c_+d_.*x_^2)),x_Symbol] :=
          (b*e-a*f)/(b*c-a*d) \\[Star] Int[1/(a+b*x^2),x] -
          (d*e-c*f)/(b*c-a*d) \\[Star] Int[1/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2))
            / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * x_.pow(2))), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (&c__ + &d__ * x_.pow(2))), x_);
            rubi_star((&b__ * &e__ - &a__ * &f__) / &determinant, first)
                    - rubi_star((&d__ * &e__ - &c__ * &f__) / determinant, second)
        },
    ));
}

fn push_rules_rule_398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 398,
        source: "Int[(e_+f_.*x_^2)/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          f/b \\[Star] Int[1/Sqrt[c+d*x^2],x] +
          (b*e-a*f)/b \\[Star] Int[1/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2))
            / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / second_base.sqrt()), x_);
            let second = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * x_.pow(2)) * second_base.sqrt())),
                x_,
            );
            rubi_star(&f__ / &b__, first)
                    + rubi_star((&b__ * &e__ - &a__ * &f__) / &b__, second)
        },
    ));
}

fn push_rules_rule_399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 399,
        source: "Int[(e_+f_.*x_^2)/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          f/b \\[Star] Int[Sqrt[a+b*x^2]/Sqrt[c+d*x^2],x] +
          (b*e-a*f)/b \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] &&
          Not[PosQ[b/a] && PosQ[d/c] || NegQ[b/a] && (PosQ[d/c] || GtQ[a,0] && (Not[GtQ[c,0]] || SimplerSqrtQ[-b/a,-d/c]))]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ + f__ * x_.pow(2))
            / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && !(posq!(&b__ / &a__) && posq!(&d__ / &c__)
                    || negq!(&b__ / &a__)
                        && (posq!(&d__ / &c__)
                            || gtq!(a__, 0)
                                && (!gtq!(c__, 0)
                                    || rubi_simpler_sqrt_q(
                                        &(-&b__ / &a__),
                                        &(-&d__ / &c__),
                                    ))))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&(first_base.sqrt() / second_base.sqrt()), x_);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (first_base.sqrt() * second_base.sqrt())),
                x_,
            );
            rubi_star(&f__ / &b__, first)
                    + rubi_star((&b__ * &e__ - &a__ * &f__) / &b__, second)
        },
    ));
}

fn push_rules_rule_401(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 401,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          -(b*e-a*f)*x*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(a*b*2*(p+1)) +
          1/(a*b*2*(p+1)) \\[Star]
            Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*Simp[c*(b*e*2*(p+1)+b*e-a*f)+d*(b*e*2*(p+1)+(b*e-a*f)*(2*q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, d__, f__, q_],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = Atom::num(2) * &a__ * &b__ * (&p_ + 1);
            let direct = -&be_af * x_ * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / &denominator;
            let payload = rubi_simp(
                &(&c__ * (Atom::num(2) * &b__ * &e__ * (&p_ + 1) + &be_af)
                    + &d__
                        * (Atom::num(2) * &b__ * &e__ * (&p_ + 1)
                            + &be_af * (Atom::num(2) * &q_ + 1))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_ - 1) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_402(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 402,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          -(b*e-a*f)*x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*2*(b*c-a*d)*(p+1)) +
          1/(a*2*(b*c-a*d)*(p+1)) \\[Star]
            Int[(a+b*x^2)^(p+1)*(c+d*x^2)^q*Simp[c*(b*e-a*f)+e*2*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(2*(p+q+2)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,q},x] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, d__, f__, q_],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_) && ltq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = Atom::num(2) * &a__ * &determinant * (&p_ + 1);
            let direct = -&be_af
                * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&c__ * &be_af
                    + Atom::num(2) * &e__ * &determinant * (&p_ + 1)
                    + &d__
                        * &be_af
                        * (Atom::num(2) * (&p_ + &q_ + 2) + 1)
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_403(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    let rule = rubi_rule!(
        order: 403,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          f*x*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(b*(2*(p+q+1)+1)) +
          1/(b*(2*(p+q+1)+1)) \\[Star]
            Int[(a+b*x^2)^p*(c+d*x^2)^(q-1)*Simp[c*(b*e-a*f+b*e*2*(p+q+1))+(d*(b*e-a*f)+f*2*q*(b*c-a*d)+b*d*e*2*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && GtQ[q,0] && NeQ[2*(p+q+1)+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, d__, f__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && gtq!(q_, 0)
                && neq!(Atom::num(2) * (&p_ + &q_ + 1) + 1, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let balance = Atom::num(2) * (&p_ + &q_ + 1) + 1;
            let direct = &f__ * x_ * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / (&b__ * &balance);
            let payload = rubi_simp(
                &(&c__ * (&be_af + Atom::num(2) * &b__ * &e__ * (&p_ + &q_ + 1))
                    + (&d__ * &be_af
                        + Atom::num(2) * &f__ * &q_ * &determinant
                        + Atom::num(2) * &b__ * &d__ * &e__ * (&p_ + &q_ + 1))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_) * second_base.pow(&q_ - 1) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * balance), primitive)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_405(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 405,
        source: "Int[(a_+b_.*x_^2)^p_*(e_+f_.*x_^2)/(c_+d_.*x_^2),x_Symbol] :=
          f/d \\[Star] Int[(a+b*x^2)^p,x] + (d*e-c*f)/d \\[Star] Int[(a+b*x^2)^p/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,p},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).pow(p_)
            * (e__ + f__ * x_.pow(2))
            / (c__ + d__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_], x_) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&first_base.pow(&p_), x_);
            let second = rubi_rhs_int(
                &(first_base.pow(&p_) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(&f__ / &d__, first)
                    + rubi_star((&d__ * &e__ - &c__ * &f__) / &d__, second)
        },
    ));
}

fn push_rules_rule_406(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    let rule = rubi_rule!(
        order: 406,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          e \\[Star] Int[(a+b*x^2)^p*(c+d*x^2)^q,x] + f \\[Star] Int[x^2*(a+b*x^2)^p*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, d__, f__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_) },
        rhs: {
            let common = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let first = rubi_rhs_int(&common, x_);
            let second = rubi_rhs_int(&(x_.pow(2) * common), x_);
            rubi_star(e__, first) + rubi_star(f__, second)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_425(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 425,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_,x_Symbol] :=
          d/b \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*(e+f*x^2)^r,x] +
          (b*c-a*d)/b \\[Star] Int[(a+b*x^2)^p*(c+d*x^2)^(q-1)*(e+f*x^2)^r,x] /;
        FreeQ[{a,b,c,d,e,f,r},x] && ILtQ[p,0] && GtQ[q,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, r_], x_)
                && iltq!(p_, 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(first_base.pow(&p_ + 1)
                    * second_base.pow(&q_ - 1)
                    * third_base.pow(&r_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(first_base.pow(&p_)
                    * second_base.pow(&q_ - 1)
                    * third_base.pow(&r_)),
                x_,
            );
            rubi_star(&d__ / &b__, first)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &b__, second)
        },
    ));
}

fn push_rules_rule_426(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 426,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_,x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(a+b*x^2)^p*(c+d*x^2)^(q+1)*(e+f*x^2)^r,x] -
          d/(b*c-a*d) \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^q*(e+f*x^2)^r,x] /;
        FreeQ[{a,b,c,d,e,f,q},x] && ILtQ[p,0] && LeQ[q,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && iltq!(p_, 0)
                && leq!(q_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let third_base = &e__ + &f__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &(first_base.pow(&p_)
                    * second_base.pow(&q_ + 1)
                    * third_base.pow(&r_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * third_base.pow(&r_)),
                x_,
            );
            rubi_star(&b__ / &determinant, first)
                    - rubi_star(&d__ / determinant, second)
        },
    ));
}

fn push_rules_rule_433(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 433,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^r,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, r_, x_],
        optional: [b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_) && {
                let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                    * (&e__ + &f__ * x_.pow(2)).pow(&r_);
                let u = rubi_expand_integrand(&integrand, x_);
                rubi_sum_q(&u)
            }
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                * (&e__ + &f__ * x_.pow(2)).pow(&r_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_434(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, r_, x_);
    let rule = rubi_rule!(
        order: 434,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2)^r_.,x_Symbol] :=
          Unintegrable[(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^r,x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, r_, x_],
        optional: [b__, d__, f__, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                * (&e__ + &f__ * x_.pow(2)).pow(&r_);
            rubi_unintegrable(integrand, x_)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
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
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_) * (e__ + f__ * x_.pow(2))
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
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_)
        * (c__ + d__ * x_.pow(2)).pow(q_)
        * (e__ + f__ * x_.pow(2)).pow(r_)
}
