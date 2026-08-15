use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2126(rules);
    push_rules_rule_2127(rules);
    push_rules_rule_2128(rules);
    push_rules_rule_2129(rules);
    push_rules_rule_2130(rules);
    push_rules_rule_2131(rules);
    push_rules_rule_2132(rules);
    push_rules_rule_2133(rules);
    push_rules_rule_2134(rules);
    push_rules_rule_2135(rules);
    push_rules_rule_2136(rules);
    push_rules_rule_2137(rules);
    push_rules_rule_2138(rules);
    push_rules_rule_2139(rules);
    push_rules_rule_2140(rules);
    push_rules_rule_2142(rules);
    push_rules_rule_2143(rules);
    push_rules_rule_2144(rules);
    push_rules_rule_2145(rules);
}

fn push_rules_rule_2126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2126,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          (c/f)^p \\[Star] Int[Px*(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && PolyQ[Px,x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) &&
          (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, p_, e__, f__, q_],
        when: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && (integerq!(p_) || gtq!(&c__ / &f__, 0))
                && (!integerq!(q_)
                    || rubi_leaf_count(&second) <= rubi_leaf_count(&first))
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &(&px__
                    * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&p_ + &q_)),
                x_,
            );

            rubi_star((&c__ / &f__).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_2127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2127,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p]) \\[Star] Int[Px*(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && PolyQ[Px,x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, p_, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && !integerq!(p_)
                && !integerq!(q_)
                && !gtq!(&c__ / &f__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let coefficient = a__.pow(rubi_int_part(&p_)) * first.pow(rubi_frac_part(&p_))
                / (d__.pow(rubi_int_part(&p_)) * second.pow(rubi_frac_part(&p_)));
            let recursive = rubi_rhs_int(&(&px__ * second.pow(&p_ + &q_)), x_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2128,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          1/c^p \\[Star] Int[Px*(b/2+c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && PolyQ[Px,x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, p_, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed = &px__
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(Atom::num(1) / c__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_2129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2129,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] :=
          1/c^p \\[Star] Int[Px*(b/2+c*x)^(2*p)*(d+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,f,p,q},x] && PolyQ[Px,x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, a__, b__, c__, p_, d__, f__, q_, x_],
        optional: [b__, c__, p_, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed = &px__
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_)
                * (&d__ + &f__ * x_.pow(2)).pow(&q_);
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(Atom::num(1) / c__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_2130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2130,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && PolyQ[Px,x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, p_, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let coefficient = first.pow(rubi_frac_part(&p_))
                / ((Atom::num(4) * &c__).pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * rubi_frac_part(&p_)));
            let transformed = linear.pow(Atom::num(2) * &p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2131,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,f,p,q},x] && PolyQ[Px,x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, a__, b__, c__, p_, d__, f__, q_, x_],
        optional: [b__, c__, p_, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let coefficient = first.pow(rubi_frac_part(&p_))
                / ((Atom::num(4) * &c__).pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * rubi_frac_part(&p_)));
            let transformed = linear.pow(Atom::num(2) * &p_)
                * (&d__ + &f__ * x_.pow(2)).pow(&q_);
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2132,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (A*b*c-2*a*B*c+a*b*C-(c*(b*B-2*A*c)-C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) -
          1/(c*(b^2-4*a*c)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[e*q*(A*b*c-2*a*B*c+a*b*C)-d*(c*(b*B-2*A*c)*(2*p+3)+C*(2*a*c-b^2*(p+2)))+
                (2*f*q*(A*b*c-2*a*B*c+a*b*C)-e*(c*(b*B-2*A*c)*(2*p+q+3)+C*(2*a*c*(q+1)-b^2*(p+q+2))))*x-
                f*(c*(b*B-2*A*c)*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x]] /;
        FreeQ[{a,b,c,d,e,f},x] && PolyQ[Px,x,2] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let abc = &capital_a * &b__ * &c__
                - Atom::num(2) * &a__ * &capital_b * &c__
                + &a__ * &b__ * &capital_c;
            let bb_two_ac = &b__ * &capital_b - Atom::num(2) * &capital_a * &c__;
            let direct_linear = &c__ * &bb_two_ac
                - &capital_c * (b__.pow(2) - Atom::num(2) * &a__ * &c__);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &c__ * &discriminant * &p_plus_one;
            let direct = (&abc - &direct_linear * x_)
                * first.pow(&p_plus_one)
                * second.pow(&q_)
                / &denominator;
            let payload = rubi_simp(
                &(&e__ * &q_ * &abc
                    - &d__
                        * (&c__ * &bb_two_ac * (Atom::num(2) * &p_ + 3)
                            + &capital_c
                                * (Atom::num(2) * &a__ * &c__
                                    - b__.pow(2) * (&p_ + 2)))
                    + (Atom::num(2) * &f__ * &q_ * &abc
                        - &e__
                            * (&c__
                                * &bb_two_ac
                                * (Atom::num(2) * &p_ + &q_ + 3)
                                + &capital_c
                                    * (Atom::num(2) * &a__ * &c__ * (&q_ + 1)
                                        - b__.pow(2) * (&p_ + &q_ + 2))))
                        * x_
                    - &f__
                        * (&c__
                            * &bb_two_ac
                            * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3)
                            + &capital_c
                                * (Atom::num(2) * &a__ * &c__ * (Atom::num(2) * &q_ + 1)
                                    - b__.pow(2) * (&p_ + Atom::num(2) * &q_ + 2)))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(p_plus_one) * second.pow(&q_ - 1) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2133,
        source: "Int[Px_*(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (a*B-(A*c-a*C)*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(2*a*c*(p+1)) -
          2/((-4*a*c)*(p+1)) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[A*c*d*(2*p+3)-a*(C*d+B*e*q)+(A*c*e*(2*p+q+3)-a*(2*B*f*q+C*e*(q+1)))*x-f*(a*C*(2*q+1)-A*c*(2*p+2*q+3))*x^2,x],x]] /;
        FreeQ[{a,c,d,e,f},x] && PolyQ[Px,x,2] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, a__, c__, p_, d__, e__, f__, q_, x_],
        optional: [c__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let direct = (&a__ * &capital_b
                - (&capital_a * &c__ - &a__ * &capital_c) * x_)
                * first.pow(&p_plus_one)
                * second.pow(&q_)
                / (Atom::num(2) * &a__ * &c__ * &p_plus_one);
            let payload = rubi_simp(
                &(&capital_a * &c__ * &d__ * (Atom::num(2) * &p_ + 3)
                    - &a__ * (&capital_c * &d__ + &capital_b * &e__ * &q_)
                    + (&capital_a * &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + 3)
                        - &a__
                            * (Atom::num(2) * &capital_b * &f__ * &q_
                                + &capital_c * &e__ * (&q_ + 1)))
                        * x_
                    - &f__
                        * (&a__ * &capital_c * (Atom::num(2) * &q_ + 1)
                            - &capital_a
                                * &c__
                                * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&p_plus_one) * second.pow(&q_ - 1) * payload),
                x_,
            );
            let coefficient = Atom::num(2)
                / ((-Atom::num(4) * &a__ * &c__) * p_plus_one);

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_2134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2134,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (A*b*c-2*a*B*c+a*b*C-(c*(b*B-2*A*c)-C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) -
          1/(c*(b^2-4*a*c)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
              Simp[-d*(c*(b*B-2*A*c)*(2*p+3)+C*(2*a*c-b^2*(p+2)))+
                (2*f*q*(A*b*c-2*a*B*c+a*b*C))*x-
                f*(c*(b*B-2*A*c)*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x]] /;
        FreeQ[{a,b,c,d,f},x] && PolyQ[Px,x,2] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, a__, b__, c__, p_, d__, f__, q_, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let abc = &capital_a * &b__ * &c__
                - Atom::num(2) * &a__ * &capital_b * &c__
                + &a__ * &b__ * &capital_c;
            let bb_two_ac = &b__ * &capital_b - Atom::num(2) * &capital_a * &c__;
            let direct_linear = &c__ * &bb_two_ac
                - &capital_c * (b__.pow(2) - Atom::num(2) * &a__ * &c__);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &c__ * &discriminant * &p_plus_one;
            let direct = (&abc - &direct_linear * x_)
                * first.pow(&p_plus_one)
                * second.pow(&q_)
                / &denominator;
            let payload = rubi_simp(
                &(-&d__
                    * (&c__ * &bb_two_ac * (Atom::num(2) * &p_ + 3)
                        + &capital_c
                            * (Atom::num(2) * &a__ * &c__
                                - b__.pow(2) * (&p_ + 2)))
                    + Atom::num(2) * &f__ * &q_ * &abc * x_
                    - &f__
                        * (&c__
                            * &bb_two_ac
                            * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3)
                            + &capital_c
                                * (Atom::num(2) * &a__ * &c__ * (Atom::num(2) * &q_ + 1)
                                    - b__.pow(2) * (&p_ + Atom::num(2) * &q_ + 2)))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(p_plus_one) * second.pow(&q_ - 1) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2135,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
            ((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+
              c*(A*(2*c^2*d+b^2*f-c*(b*e+2*a*f))-B*(b*c*d-2*a*c*e+a*b*f)+C*(b^2*d-a*b*e-2*a*(c*d-a*f)))*x) +
          1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[(b*B-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)+
                (b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
                e*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
                (2*f*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
                  (b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*
                  (b*f*(p+1)-c*e*(2*p+q+4)))*x-
                c*f*(b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(2*p+2*q+5)*x^2,x],x]] /;
        FreeQ[{a,b,c,d,e,f,q},x] && PolyQ[Px,x,2] && LtQ[p,-1] && NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            let resultant = (&c__ * &d__ - &a__ * &f__).pow(2)
                - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && neq!(resultant, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let resultant = (&c__ * &d__ - &a__ * &f__).pow(2)
                - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &discriminant * &resultant * &p_plus_one;
            let alpha = (&capital_a * &c__ - &a__ * &capital_c)
                * (Atom::num(2) * &a__ * &c__ * &e__
                    - &b__ * (&c__ * &d__ + &a__ * &f__))
                + (&capital_a * &b__ - &a__ * &capital_b)
                    * (Atom::num(2) * c__.pow(2) * &d__
                        + b__.pow(2) * &f__
                        - &c__ * (&b__ * &e__ + Atom::num(2) * &a__ * &f__));
            let beta = b__.pow(2) * (&capital_c * &d__ + &capital_a * &f__)
                - &b__
                    * (&capital_b * &c__ * &d__
                        + &capital_a * &c__ * &e__
                        + &a__ * &capital_c * &e__
                        + &a__ * &capital_b * &f__)
                + Atom::num(2)
                    * (&capital_a * &c__ * (&c__ * &d__ - &a__ * &f__)
                        - &a__
                            * (&c__ * &capital_c * &d__
                                - &capital_b * &c__ * &e__
                                - &a__ * &capital_c * &f__));
            let gamma = &capital_a
                * (Atom::num(2) * c__.pow(2) * &d__
                    + b__.pow(2) * &f__
                    - &c__ * (&b__ * &e__ + Atom::num(2) * &a__ * &f__))
                - &capital_b
                    * (&b__ * &c__ * &d__
                        - Atom::num(2) * &a__ * &c__ * &e__
                        + &a__ * &b__ * &f__)
                + &capital_c
                    * (b__.pow(2) * &d__
                        - &a__ * &b__ * &e__
                        - Atom::num(2) * &a__ * (&c__ * &d__ - &a__ * &f__));
            let direct = first.pow(&p_plus_one)
                * second.pow(&q_ + 1)
                * (&alpha + &c__ * &gamma * x_)
                / &denominator;
            let payload = rubi_simp(
                &((&b__ * &capital_b
                    - Atom::num(2) * &capital_a * &c__
                    - Atom::num(2) * &a__ * &capital_c)
                    * &resultant
                    * &p_plus_one
                    + &beta
                        * (&a__ * &f__ * &p_plus_one - &c__ * &d__ * (&p_ + 2))
                    - &e__ * &alpha * (&p_ + &q_ + 2)
                    - (Atom::num(2) * &f__ * &alpha * (&p_ + &q_ + 2)
                        - &beta
                            * (&b__ * &f__ * &p_plus_one
                                - &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + 4)))
                        * x_
                    - &c__
                        * &f__
                        * &beta
                        * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 5)
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(p_plus_one) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2136,
        source: "Int[Px_*(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
            ((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d-c*(2*a*f))+
              c*(A*(2*c^2*d-c*(2*a*f))-B*(-2*a*c*e)+C*(-2*a*(c*d-a*f)))*x) +
          1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1)) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[(-2*A*c-2*a*C)*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)+
                (2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
                e*((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d-c*(+2*a*f)))*(p+q+2)-
                (2*f*((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d+-c*(+2*a*f)))*(p+q+2)-
                  (2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*
                  (-c*e*(2*p+q+4)))*x-
                c*f*(2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(2*p+2*q+5)*x^2,x],x]] /;
        FreeQ[{a,c,d,e,f,q},x] && PolyQ[Px,x,2] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, a__, c__, p_, d__, e__, f__, q_, x_],
        optional: [c__, e__, f__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            let resultant = &a__ * &c__ * e__.pow(2)
                + (&c__ * &d__ - &a__ * &f__).pow(2);
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && neq!(resultant, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let resultant = &a__ * &c__ * e__.pow(2)
                + (&c__ * &d__ - &a__ * &f__).pow(2);
            let denominator = (-Atom::num(4) * &a__ * &c__) * &resultant * &p_plus_one;
            let alpha = (&capital_a * &c__ - &a__ * &capital_c)
                * (Atom::num(2) * &a__ * &c__ * &e__)
                + (-&a__ * &capital_b)
                    * (Atom::num(2) * c__.pow(2) * &d__
                        - &c__ * (Atom::num(2) * &a__ * &f__));
            let beta = Atom::num(2)
                * (&capital_a * &c__ * (&c__ * &d__ - &a__ * &f__)
                    - &a__
                        * (&c__ * &capital_c * &d__
                            - &capital_b * &c__ * &e__
                            - &a__ * &capital_c * &f__));
            let gamma = &capital_a
                * (Atom::num(2) * c__.pow(2) * &d__
                    - &c__ * (Atom::num(2) * &a__ * &f__))
                - &capital_b * (-Atom::num(2) * &a__ * &c__ * &e__)
                + &capital_c * (-Atom::num(2) * &a__ * (&c__ * &d__ - &a__ * &f__));
            let direct = first.pow(&p_plus_one)
                * second.pow(&q_ + 1)
                * (&alpha + &c__ * &gamma * x_)
                / &denominator;
            let payload = rubi_simp(
                &((-Atom::num(2) * &capital_a * &c__
                    - Atom::num(2) * &a__ * &capital_c)
                    * &resultant
                    * &p_plus_one
                    + &beta
                        * (&a__ * &f__ * &p_plus_one - &c__ * &d__ * (&p_ + 2))
                    - &e__ * &alpha * (&p_ + &q_ + 2)
                    - (Atom::num(2) * &f__ * &alpha * (&p_ + &q_ + 2)
                        - &beta
                            * (-&c__ * &e__ * (Atom::num(2) * &p_ + &q_ + 4)))
                        * x_
                    - &c__
                        * &f__
                        * &beta
                        * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 5)
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(p_plus_one) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2137,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
            ((A*c-a*C)*(-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(2*a*f))+
              c*(A*(2*c^2*d+b^2*f-c*(2*a*f))-B*(b*c*d+a*b*f)+C*(b^2*d-2*a*(c*d-a*f)))*x) +
          1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
              Simp[(b*B-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d)*(-b*f))*(p+1)+
                (b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
                (2*f*((A*c-a*C)*(-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(2*a*f)))*(p+q+2)-
                  (b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*
                  (b*f*(p+1)))*x-
                c*f*(b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(2*p+2*q+5)*x^2,x],x]] /;
        FreeQ[{a,b,c,d,f,q},x] && PolyQ[Px,x,2] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, a__, b__, c__, p_, d__, f__, q_, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__, q_],
        when: {
            let resultant = b__.pow(2) * &d__ * &f__
                + (&c__ * &d__ - &a__ * &f__).pow(2);
            rubi_poly_q_degree(&px__, x_, 2)
                && ltq!(p_, -1)
                && neq!(resultant, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let p_plus_one = &p_ + 1;
            let resultant = b__.pow(2) * &d__ * &f__
                + (&c__ * &d__ - &a__ * &f__).pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &discriminant * &resultant * &p_plus_one;
            let alpha = (&capital_a * &c__ - &a__ * &capital_c)
                * (-&b__ * (&c__ * &d__ + &a__ * &f__))
                + (&capital_a * &b__ - &a__ * &capital_b)
                    * (Atom::num(2) * c__.pow(2) * &d__
                        + b__.pow(2) * &f__
                        - &c__ * (Atom::num(2) * &a__ * &f__));
            let beta = b__.pow(2) * (&capital_c * &d__ + &capital_a * &f__)
                - &b__
                    * (&capital_b * &c__ * &d__ + &a__ * &capital_b * &f__)
                + Atom::num(2)
                    * (&capital_a * &c__ * (&c__ * &d__ - &a__ * &f__)
                        - &a__
                            * (&c__ * &capital_c * &d__
                                - &a__ * &capital_c * &f__));
            let gamma = &capital_a
                * (Atom::num(2) * c__.pow(2) * &d__
                    + b__.pow(2) * &f__
                    - &c__ * (Atom::num(2) * &a__ * &f__))
                - &capital_b * (&b__ * &c__ * &d__ + &a__ * &b__ * &f__)
                + &capital_c
                    * (b__.pow(2) * &d__
                        - Atom::num(2) * &a__ * (&c__ * &d__ - &a__ * &f__));
            let direct = first.pow(&p_plus_one)
                * second.pow(&q_ + 1)
                * (&alpha + &c__ * &gamma * x_)
                / &denominator;
            let payload = rubi_simp(
                &((&b__ * &capital_b
                    - Atom::num(2) * &capital_a * &c__
                    - Atom::num(2) * &a__ * &capital_c)
                    * &resultant
                    * &p_plus_one
                    + &beta
                        * (&a__ * &f__ * &p_plus_one - &c__ * &d__ * (&p_ + 2))
                    - (Atom::num(2) * &f__ * &alpha * (&p_ + &q_ + 2)
                        - &beta * (&b__ * &f__ * &p_plus_one))
                        * x_
                    - &c__
                        * &f__
                        * &beta
                        * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + 5)
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(p_plus_one) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2138,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (B*c*f*(2*p+2*q+3)+C*(b*f*p-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
            (d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) -
          (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3))) \\[Star]
            Int[(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
              Simp[p*(b*d-a*e)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(B*e-2*A*f)*(2*p+2*q+3)))+
                (2*p*(c*d-a*f)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(C*e*f*p*(b^2-4*a*c)-b*c*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x+
                (p*(c*e-b*f)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x^2,x],x]] /;
        FreeQ[{a,b,c,d,e,f,q},x] && PolyQ[Px,x,2] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, d__, e__, f__, q_, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + 1, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3, 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let sum = &p_ + &q_ + 1;
            let twice_sum_plus_three = Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3;
            let two_p_q_plus_two = Atom::num(2) * &p_ + &q_ + 2;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let delta = &capital_c * (&c__ * &e__ - &b__ * &f__) * (&q_ + 1)
                - &c__
                    * (&capital_c * &e__ - &capital_b * &f__)
                    * &twice_sum_plus_three;
            let eta = &capital_c
                * (e__.pow(2) - Atom::num(4) * &d__ * &f__)
                * &two_p_q_plus_two
                + &f__
                    * (Atom::num(2) * &capital_c * &d__
                        - &capital_b * &e__
                        + Atom::num(2) * &capital_a * &f__)
                    * &twice_sum_plus_three;
            let denominator = Atom::num(2)
                * &c__
                * f__.pow(2)
                * &sum
                * &twice_sum_plus_three;
            let direct_numerator = &capital_b * &c__ * &f__ * &twice_sum_plus_three
                + &capital_c
                    * (&b__ * &f__ * &p_ - &c__ * &e__ * &two_p_q_plus_two)
                + Atom::num(2)
                    * &c__
                    * &capital_c
                    * &f__
                    * &sum
                    * x_;
            let direct = direct_numerator * first.pow(&p_) * second.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&p_ * (&b__ * &d__ - &a__ * &e__) * &delta
                    + &sum
                        * (b__.pow(2) * &capital_c * &d__ * &f__ * &p_
                            + &a__
                                * &c__
                                * (&capital_c
                                    * (Atom::num(2) * &d__ * &f__
                                        - e__.pow(2) * &two_p_q_plus_two)
                                    + &f__
                                        * (&capital_b * &e__
                                            - Atom::num(2) * &capital_a * &f__)
                                        * &twice_sum_plus_three))
                    + (Atom::num(2)
                        * &p_
                        * (&c__ * &d__ - &a__ * &f__)
                        * &delta
                        + &sum
                            * (&capital_c * &e__ * &f__ * &p_ * &discriminant
                                - &b__ * &c__ * &eta))
                        * x_
                    + (&p_ * (&c__ * &e__ - &b__ * &f__) * &delta
                        + &sum
                            * (&capital_c * f__.pow(2) * &p_ * &discriminant
                                - c__.pow(2) * &eta))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&p_ - 1) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2139,
        source: "Int[Px_*(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (B*c*f*(2*p+2*q+3)+C*(-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+c*x^2)^p*
            (d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) -
          (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3))) \\[Star]
            Int[(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
              Simp[p*(-a*e)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(B*e-2*A*f)*(2*p+2*q+3)))+
                (2*p*(c*d-a*f)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(C*e*f*p*(-4*a*c)))*x+
                (p*(c*e)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(C*f^2*p*(-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x^2,x],x]] /;
        FreeQ[{a,c,d,e,f,q},x] && PolyQ[Px,x,2] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, a__, c__, p_, d__, e__, f__, q_, x_],
        optional: [c__, e__, f__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + 1, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3, 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let sum = &p_ + &q_ + 1;
            let twice_sum_plus_three = Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3;
            let two_p_q_plus_two = Atom::num(2) * &p_ + &q_ + 2;
            let delta = &capital_c * &c__ * &e__ * (&q_ + 1)
                - &c__
                    * (&capital_c * &e__ - &capital_b * &f__)
                    * &twice_sum_plus_three;
            let eta = &capital_c
                * (e__.pow(2) - Atom::num(4) * &d__ * &f__)
                * &two_p_q_plus_two
                + &f__
                    * (Atom::num(2) * &capital_c * &d__
                        - &capital_b * &e__
                        + Atom::num(2) * &capital_a * &f__)
                    * &twice_sum_plus_three;
            let denominator = Atom::num(2)
                * &c__
                * f__.pow(2)
                * &sum
                * &twice_sum_plus_three;
            let direct_numerator = &capital_b * &c__ * &f__ * &twice_sum_plus_three
                - &capital_c * &c__ * &e__ * &two_p_q_plus_two
                + Atom::num(2)
                    * &c__
                    * &capital_c
                    * &f__
                    * &sum
                    * x_;
            let direct = direct_numerator * first.pow(&p_) * second.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&p_ * (-&a__ * &e__) * &delta
                    + &sum
                        * (&a__
                            * &c__
                            * (&capital_c
                                * (Atom::num(2) * &d__ * &f__
                                    - e__.pow(2) * &two_p_q_plus_two)
                                + &f__
                                    * (&capital_b * &e__
                                        - Atom::num(2) * &capital_a * &f__)
                                    * &twice_sum_plus_three))
                    + (Atom::num(2)
                        * &p_
                        * (&c__ * &d__ - &a__ * &f__)
                        * &delta
                        + &sum
                            * (&capital_c
                                * &e__
                                * &f__
                                * &p_
                                * (-Atom::num(4) * &a__ * &c__)))
                        * x_
                    + (&p_ * &c__ * &e__ * &delta
                        + &sum
                            * (&capital_c
                                * f__.pow(2)
                                * &p_
                                * (-Atom::num(4) * &a__ * &c__)
                                - c__.pow(2) * &eta))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&p_ - 1) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2140,
        source: "Int[Px_*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          (B*c*f*(2*p+2*q+3)+C*(b*f*p)+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
            (d+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) -
          (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3))) \\[Star]
            Int[(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^q*
              Simp[p*(b*d)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f)+f*(-2*A*f)*(2*p+2*q+3)))+
                (2*p*(c*d-a*f)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(-b*c*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x+
                (p*(-b*f)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
                  (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x^2,x],x]] /;
        FreeQ[{a,b,c,d,f,q},x] && PolyQ[Px,x,2] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, a__, b__, c__, p_, d__, f__, q_, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__, q_],
        when: {
            rubi_poly_q_degree(&px__, x_, 2)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + 1, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3, 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let sum = &p_ + &q_ + 1;
            let twice_sum_plus_three = Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3;
            let two_p_q_plus_two = Atom::num(2) * &p_ + &q_ + 2;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let delta = &capital_c * (-&b__ * &f__) * (&q_ + 1)
                - &c__ * (-&capital_b * &f__) * &twice_sum_plus_three;
            let eta = &capital_c
                * (-Atom::num(4) * &d__ * &f__)
                * &two_p_q_plus_two
                + &f__
                    * (Atom::num(2) * &capital_c * &d__
                        + Atom::num(2) * &capital_a * &f__)
                    * &twice_sum_plus_three;
            let denominator = Atom::num(2)
                * &c__
                * f__.pow(2)
                * &sum
                * &twice_sum_plus_three;
            let direct_numerator = &capital_b * &c__ * &f__ * &twice_sum_plus_three
                + &capital_c * &b__ * &f__ * &p_
                + Atom::num(2)
                    * &c__
                    * &capital_c
                    * &f__
                    * &sum
                    * x_;
            let direct = direct_numerator * first.pow(&p_) * second.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&p_ * &b__ * &d__ * &delta
                    + &sum
                        * (b__.pow(2) * &capital_c * &d__ * &f__ * &p_
                            + &a__
                                * &c__
                                * (Atom::num(2) * &capital_c * &d__ * &f__
                                    - Atom::num(2)
                                        * &capital_a
                                        * f__.pow(2)
                                        * &twice_sum_plus_three))
                    + (Atom::num(2)
                        * &p_
                        * (&c__ * &d__ - &a__ * &f__)
                        * &delta
                        - &sum * &b__ * &c__ * &eta)
                        * x_
                    + (&p_ * (-&b__ * &f__) * &delta
                        + &sum
                            * (&capital_c * f__.pow(2) * &p_ * &discriminant
                                - c__.pow(2) * &eta))
                        * x_.pow(2)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&p_ - 1) * second.pow(&q_) * payload),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px_, a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 2142,
        source: "Int[Px_/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],q=c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2},
          1/q \\[Star] Int[(A*c^2*d-a*c*C*d+A*b^2*f-a*b*B*f-a*A*c*f+a^2*C*f+c*(B*c*d-b*C*d+A*b*f-a*B*f)*x)/(a+b*x+c*x^2),x] +
          1/q \\[Star] Int[(c*C*d^2+b*B*d*f-A*c*d*f-a*C*d*f+a*A*f^2-f*(B*c*d-b*C*d+A*b*f-a*B*f)*x)/(d+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,f},x] && PolyQ[Px,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px_ / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2))),
        with: [px_, a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            let q = c__.pow(2) * d__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                + a__.pow(2) * f__.pow(2);
            rubi_poly_q_degree(&px_, x_, 2) && neq!(q, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let q = c__.pow(2) * d__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                + a__.pow(2) * f__.pow(2);
            let shared_linear = &capital_b * &c__ * &d__
                - &b__ * &capital_c * &d__
                + &capital_a * &b__ * &f__
                - &a__ * &capital_b * &f__;
            let first_numerator = &capital_a * c__.pow(2) * &d__
                - &a__ * &c__ * &capital_c * &d__
                + &capital_a * b__.pow(2) * &f__
                - &a__ * &b__ * &capital_b * &f__
                - &a__ * &capital_a * &c__ * &f__
                + a__.pow(2) * &capital_c * &f__
                + &c__ * &shared_linear * x_;
            let second_numerator = &c__ * &capital_c * d__.pow(2)
                + &b__ * &capital_b * &d__ * &f__
                - &capital_a * &c__ * &d__ * &f__
                - &a__ * &capital_c * &d__ * &f__
                + &a__ * &capital_a * f__.pow(2)
                - &f__ * shared_linear * x_;
            let first_integrand = first_numerator
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let second_integrand =
                second_numerator / (&d__ + &f__ * x_.pow(2));

            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2143,
        source: "Int[Px_/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          C/c \\[Star] Int[1/Sqrt[d+e*x+f*x^2],x] + 1/c \\[Star] Int[(A*c-a*C+(B*c-b*C)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && PolyQ[Px,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px_
            / ((a__ + b__ * x_ + c__ * x_.pow(2))
                * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt()),
        with: [px_, a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: { rubi_poly_q_degree(&px_, x_, 2) },
        rhs: {
            let capital_a = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let remainder = &capital_a * &c__ - &a__ * &capital_c
                + (&capital_b * &c__ - &b__ * &capital_c) * x_;

            rubi_star(&capital_c / &c__, rubi_rhs_int(&(Atom::num(1) / second.sqrt()), x_)) + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(remainder / (first * second.sqrt())), x_))
        },
    ));
}

fn push_rules_rule_2144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px_, a__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2144,
        source: "Int[Px_/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          C/c \\[Star] Int[1/Sqrt[d+e*x+f*x^2],x] + 1/c \\[Star] Int[(A*c-a*C+B*c*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,c,d,e,f},x] && PolyQ[Px,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px_
            / ((a__ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt()),
        with: [px_, a__, c__, d__, e__, f__, x_],
        optional: [c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: { rubi_poly_q_degree(&px_, x_, 2) },
        rhs: {
            let capital_a = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let remainder =
                &capital_a * &c__ - &a__ * &capital_c + &capital_b * &c__ * x_;

            rubi_star(&capital_c / &c__, rubi_rhs_int(&(Atom::num(1) / second.sqrt()), x_)) + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(remainder / (first * second.sqrt())), x_))
        },
    ));
}

fn push_rules_rule_2145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px_, a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 2145,
        source: "Int[Px_/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
          C/c \\[Star] Int[1/Sqrt[d+f*x^2],x] + 1/c \\[Star] Int[(A*c-a*C+(B*c-b*C)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f},x] && PolyQ[Px,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px_
            / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2)).sqrt()),
        with: [px_, a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: { rubi_poly_q_degree(&px_, x_, 2) },
        rhs: {
            let capital_a = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let remainder = &capital_a * &c__ - &a__ * &capital_c
                + (&capital_b * &c__ - &b__ * &capital_c) * x_;

            rubi_star(&capital_c / &c__, rubi_rhs_int(&(Atom::num(1) / second.sqrt()), x_)) + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(remainder / (first * second.sqrt())), x_))
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
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (d__ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (a__ + c__ * x_.pow(2)).pow(p_) * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
}
