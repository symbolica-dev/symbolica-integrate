use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_724(rules);
    push_rules_rule_725(rules);
    push_rules_rule_726(rules);
    push_rules_rule_727(rules);
    push_rules_rule_728(rules);
    push_rules_rule_729(rules);
    push_rules_rule_730(rules);
    push_rules_rule_731(rules);
    push_rules_rule_732(rules);
    push_rules_rule_733(rules);
    push_rules_rule_734(rules);
    push_rules_rule_735(rules);
    push_rules_rule_736(rules);
    push_rules_rule_737(rules);
    push_rules_rule_738(rules);
    push_rules_rule_739(rules);
    push_rules_rule_740(rules);
    push_rules_rule_741(rules);
    push_rules_rule_742(rules);
    push_rules_rule_743(rules);
    push_rules_rule_744(rules);
    push_rules_rule_745(rules);
}

fn push_rules_rule_724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 724,
        source: "Int[Sqrt[a_+c_.*x_^2]/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]),x_Symbol] :=
          (c*d^2+a*e^2)/e^2 \\[Star] Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] -
          1/e^2 \\[Star] Int[(c*d-c*e*x)/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + c__ * x_.pow(2)).sqrt() / ((d__ + e__ * x_) * (f__ + g__ * x_).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&linear * binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &((&c__ * &d__ - &c__ * &e__ * x_)
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let denominator = e__.pow(2);
            rubi_star(&invariant / &denominator, first)
                    - rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_725(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 725,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[a_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
          (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(e*f-d*g)) -
          1/(2*(m+1)*(e*f-d*g)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[a*g*(2*m+3)+2*(c*f)*x+c*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + c__ * x_.pow(2)).sqrt() / (f__ + g__ * x_).sqrt(),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let payload = rubi_simp(
                &(&a__ * &g__ * (Atom::num(2) * &m_ + 3)
                    + Atom::num(2) * &c__ * &f__ * x_
                    + &c__ * &g__ * (Atom::num(2) * &m_ + 5) * x_.pow(2)),
                x_,
            );
            let denominator = &m_plus_one * (&e__ * &f__ - &d__ * &g__);
            let direct = linear.pow(&m_plus_one) * binomial.sqrt() * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(m_plus_one) * payload / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_726(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 726,
        source: "Int[Sqrt[d_.+e_.*x_]/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-4*a*c,2]},
          Sqrt[2]*Sqrt[2*c*f-g*q]*Sqrt[-q+2*c*x]*(d+e*x)*
            Sqrt[(e*f-d*g)*(q+2*c*x)/((2*c*f-g*q)*(d+e*x))]*
            Sqrt[(e*f-d*g)*(2*a+q*x)/((q*f-2*a*g)*(d+e*x))]/
           (g*Sqrt[2*c*d-e*q]*Sqrt[2*a*c/q+c*x]*Sqrt[a+c*x^2])*
            EllipticPi[e*(2*c*f-g*q)/(g*(2*c*d-e*q)),
              ArcSin[Sqrt[2*c*d-e*q]*Sqrt[f+g*x]/(Sqrt[2*c*f-g*q]*Sqrt[d+e*x])],
              (q*d-2*a*e)*(2*c*f-g*q)/((q*f-2*a*g)*(2*c*d-e*q))]] /;
        FreeQ[{a,c,d,e,f,g},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt() / ((f__ + g__ * x_).sqrt() * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let q = rubi_rt(&(-Atom::num(4) * &a__ * &c__), 2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let trinomial = &a__ + &c__ * x_.pow(2);
            let two_cf_gq = Atom::num(2) * &c__ * &f__ - &g__ * &q;
            let two_cd_eq = Atom::num(2) * &c__ * &d__ - &e__ * &q;
            let qf_2ag = &q * &f__ - Atom::num(2) * &a__ * &g__;

            rubi_simp(&(Atom::num(2).sqrt()
                    * two_cf_gq.sqrt()
                    * (-&q + Atom::num(2) * &c__ * x_).sqrt()
                    * &linear
                    * (&ef_dg * (&q + Atom::num(2) * &c__ * x_) / (&two_cf_gq * &linear)).sqrt()
                    * (&ef_dg * (Atom::num(2) * &a__ + &q * x_) / (&qf_2ag * &linear)).sqrt()
                    * rubi_elliptic_pi(
                        &e__ * &two_cf_gq / (&g__ * &two_cd_eq),
                        (two_cd_eq.sqrt() * binomial.sqrt() / (two_cf_gq.sqrt() * linear.sqrt())).asin(),
                        (&q * &d__ - Atom::num(2) * &a__ * &e__) * &two_cf_gq / (&qf_2ag * &two_cd_eq),
                    )
                    / (&g__
                        * two_cd_eq.sqrt()
                        * (Atom::num(2) * &a__ * &c__ / &q + &c__ * x_).sqrt()
                        * trinomial.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 727,
        source: "Int[(d_.+e_.*x_)^(3/2)/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          e/g \\[Star] Int[Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[a+c*x^2],x] -
          (e*f-d*g)/g \\[Star] Int[Sqrt[d+e*x]/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(Atom::num(3) / Atom::num(2)) / ((f__ + g__ * x_).sqrt() * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let first = rubi_rhs_int(
                &(linear.sqrt() * binomial.sqrt() / quadratic.sqrt()),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.sqrt() / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&e__ / &g__, first)
                    - rubi_star(&ef_dg / &g__, second)
        },
    ));
}

fn push_rules_rule_728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 728,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          2*e^2*(d+e*x)^(m-2)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(c*g*(2*m-1)) -
          1/(c*g*(2*m-1)) \\[Star] Int[(d+e*x)^(m-3)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[a*e^2*(d*g+2*e*f*(m-2))-c*d^3*g*(2*m-1)+e*(e*(a*e*g*(2*m-3))+c*d*(2*e*f-3*d*g*(2*m-1)))*x+2*e^2*(c*e*f-3*c*d*g)*(m-1)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && GeQ[m,2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && geq!(m_, 2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&a__ * e__.pow(2) * (&d__ * &g__ + Atom::num(2) * &e__ * &f__ * (&m_ - 2))
                    - &c__ * d__.pow(3) * &g__ * (Atom::num(2) * &m_ - 1)
                    + &e__ * (&e__ * (&a__ * &e__ * &g__ * (Atom::num(2) * &m_ - 3))
                        + &c__ * &d__ * (Atom::num(2) * &e__ * &f__ - Atom::num(3) * &d__ * &g__ * (Atom::num(2) * &m_ - 1))) * x_
                        + Atom::num(2) * e__.pow(2) * (&c__ * &e__ * &f__ - Atom::num(3) * &c__ * &d__ * &g__) * (&m_ - 1) * x_.pow(2)),
                x_,
            );
            let denominator = &c__ * &g__ * (Atom::num(2) * &m_ - Atom::num(1));
            let direct = Atom::num(2)
                * e__.pow(2)
                * linear.pow(&m_ - Atom::num(2))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(3)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 729,
        source: "Int[1/(Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          2 \\[Star] Subst[Int[1/((d*e-c*f+f*x^2)*Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2]),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_) && posq!(&b__ / &a__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&d__ * &e__ - &c__ * &f__ + &f__ * sub_atom.pow(2))
                        * ((&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                            - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                            + &b__ * sub_atom.pow(4) / d__.pow(2))
                        .sqrt())),
                sub,
            );
            let substitution = (&c__ + &d__ * x_).sqrt();
            let substituted = rubi_subst(&transformed, sub, substitution);
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 730,
        source: "Int[1/(Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          1/Sqrt[a] \\[Star] Int[1/((e+f*x)*Sqrt[c+d*x]*Sqrt[1-q*x]*Sqrt[1+q*x]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NegQ[b/a] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && negq!(&b__ / &a__)
                && gtq!(a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&e__ + &f__ * x_)
                    * (&c__ + &d__ * x_).sqrt()
                    * (Atom::num(1) - &q * x_).sqrt()
                    * (Atom::num(1) + &q * x_).sqrt())),
                x_,
            );
            rubi_star(Atom::num(1) / a__.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 731,
        source: "Int[1/(Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[1/((e+f*x)*Sqrt[c+d*x]*Sqrt[1-q*x]*Sqrt[1+q*x]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NegQ[b/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && negq!(&b__ / &a__)
                && !gtq!(a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&e__ + &f__ * x_)
                    * (&c__ + &d__ * x_).sqrt()
                    * (Atom::num(1) - &q * x_).sqrt()
                    * (Atom::num(1) + &q * x_).sqrt())),
                x_,
            );
            let coefficient = (Atom::num(1) + &b__ * x_.pow(2) / &a__).sqrt()
                / (&a__ + &b__ * x_.pow(2)).sqrt();
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 732,
        source: "Int[1/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -2*(c+d*x)*Sqrt[(d*e-c*f)^2*(a+b*x^2)/((b*e^2+a*f^2)*(c+d*x)^2)]/((d*e-c*f)*Sqrt[a+b*x^2]) \\[Star]
          Subst[Int[1/Sqrt[Simp[1-(2*b*c*e+2*a*d*f)*x^2/(b*e^2+a*f^2)+(b*c^2+a*d^2)*x^4/(b*e^2+a*f^2),x]],x],x,Sqrt[e+f*x]/Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1)
            / ((c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_linear = &c__ + &d__ * x_;
            let second_linear = &e__ + &f__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let invariant = &b__ * e__.pow(2) + &a__ * f__.pow(2);
            let determinant = &d__ * &e__ - &c__ * &f__;
            let coefficient = -Atom::num(2)
                * &first_linear
                * (determinant.pow(2) * &quadratic
                    / (&invariant * first_linear.pow(2)))
                .sqrt()
                / (&determinant * quadratic.sqrt());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_simp(
                &(Atom::num(1)
                    - (Atom::num(2) * &b__ * &c__ * &e__
                        + Atom::num(2) * &a__ * &d__ * &f__)
                        * sub_atom.pow(2)
                        / &invariant
                    + (&b__ * c__.pow(2) + &a__ * d__.pow(2)) * sub_atom.pow(4)
                        / &invariant),
                sub,
            );
            let transformed = rubi_rhs_int(&(Atom::num(1) / payload.sqrt()), sub);
            let substitution = second_linear.sqrt() / first_linear.sqrt();
            let substituted = rubi_subst(&transformed, sub, substitution);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 733,
        source: "Int[1/(Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/2)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          d/(d*e-c*f) \\[Star] Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[a+b*x^2]),x] -
          f/(d*e-c*f) \\[Star] Int[Sqrt[c+d*x]/((e+f*x)^(3/2)*Sqrt[a+b*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: Atom::num(1)
            / ((c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).pow(Atom::num(3) / 2)
                * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let first_linear = &c__ + &d__ * x_;
            let second_linear = &e__ + &f__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let determinant = &d__ * &e__ - &c__ * &f__;
            let first = rubi_rhs_int(
                &(Atom::num(1)
                    / (first_linear.sqrt() * second_linear.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &(first_linear.sqrt()
                    / (second_linear.pow(Atom::num(3) / 2) * quadratic.sqrt())),
                x_,
            );
            rubi_star(&d__ / &determinant, first)
                    - rubi_star(&f__ / determinant, second)
        },
    ));
}

fn push_rules_rule_734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 734,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          e^2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(e*f-d*g)*(c*d^2+a*e^2)) +
          1/(2*(m+1)*(e*f-d*g)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[2*c*d*(e*f-d*g)*(m+1)-a*e^2*g*(2*m+3)+2*c*e*(d*g*(m+1)-e*f*(m+2))*x-c*e^2*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && LeQ[m,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && leq!(m_, -2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &ef_dg * &invariant;
            let payload = rubi_simp(
                &(Atom::num(2) * &d__ * (&c__ * &e__ * &f__ - &c__ * &d__ * &g__) * (&m_ + Atom::num(1))
                    - &a__ * e__.pow(2) * &g__ * (Atom::num(2) * &m_ + Atom::num(3))
                    + Atom::num(2)
                        * &e__
                        * (&c__ * &d__ * &g__ * (&m_ + Atom::num(1)) - &c__ * &e__ * &f__ * (&m_ + Atom::num(2)))
                        * x_
                    - &c__ * e__.pow(2) * &g__ * (Atom::num(2) * &m_ + Atom::num(5)) * x_.pow(2)),
                x_,
            );
            let direct = e__.pow(2)
                * linear.pow(&m_ + Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ + Atom::num(1)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 735,
        source: "Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_+c_.*x_^2],x_Symbol] :=
          2*e*(d+e*x)^(m-1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(c*(2*m+1)) -
          1/(c*(2*m+1)) \\[Star] Int[(d+e*x)^(m-2)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[a*e*(d*g+2*e*f*(m-1))-c*d^2*f*(2*m+1)+(a*e^2*g*(2*m-1)-c*d*(4*e*f*m+d*g*(2*m+1)))*x-c*e*(e*f+d*g*(4*m-1))*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && GtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&a__ * &e__ * (&d__ * &g__ + Atom::num(2) * &e__ * &f__ * (&m_ - Atom::num(1)))
                    - &c__ * d__.pow(2) * &f__ * (Atom::num(2) * &m_ + Atom::num(1))
                    + (&a__ * e__.pow(2) * &g__ * (Atom::num(2) * &m_ - Atom::num(1))
                        - &c__ * &d__ * (Atom::num(4) * &e__ * &f__ * &m_ + &d__ * &g__ * (Atom::num(2) * &m_ + Atom::num(1))))
                        * x_
                    - &c__ * &e__ * (&e__ * &f__ + &d__ * &g__ * (Atom::num(4) * &m_ - Atom::num(1))) * x_.pow(2)),
                x_,
            );
            let denominator = &c__ * (Atom::num(2) * &m_ + Atom::num(1));
            let direct = Atom::num(2)
                * &e__
                * linear.pow(&m_ - Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(2)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 736,
        source: "Int[Sqrt[f_.+g_.*x_]/((d_.+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          g/e \\[Star] Int[1/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] +
          (e*f-d*g)/e \\[Star] Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).sqrt() / ((d__ + e__ * x_) * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &(Atom::num(1) / (linear * binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&g__ / &e__, first)
                    + rubi_star((&e__ * &f__ - &d__ * &g__) / &e__, second)
        },
    ));
}

fn push_rules_rule_737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 737,
        source: "Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(c*d^2+a*e^2)) +
          1/(2*(m+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[2*c*d*f*(m+1)-e*(a*g)+2*c*(d*g*(m+1)-e*f*(m+2))*x-c*e*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && LeQ[m,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && leq!(m_, -2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let payload = rubi_simp(
                &(Atom::num(2) * &c__ * &d__ * &f__ * (&m_ + Atom::num(1))
                    - &e__ * (&a__ * &g__)
                    + Atom::num(2) * &c__ * (&d__ * &g__ * (&m_ + Atom::num(1)) - &e__ * &f__ * (&m_ + Atom::num(2))) * x_
                    - &c__ * &e__ * &g__ * (Atom::num(2) * &m_ + Atom::num(5)) * x_.pow(2)),
                x_,
            );
            let direct = &e__
                * linear.pow(&m_ + Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ + Atom::num(1)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 738,
        source: "Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          (c*d^2+a*e^2)/(e*(e*f-d*g)) \\[Star] Int[(f+g*x)^(n+1)*(a+c*x^2)^(p-1)/(d+e*x),x] -
          1/(e*(e*f-d*g)) \\[Star] Int[(f+g*x)^n*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^(p-1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && GtQ[p,0] && LtQ[n,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && !integerq!(n_)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let factor = &c__ * &d__ * &f__ + &a__ * &e__ * &g__ - &c__ * &ef_dg * x_;
            let first = rubi_rhs_int(
                &(binomial.pow(&n_ + Atom::num(1))
                    * quadratic.pow(&p_ - Atom::num(1))
                    / &linear),
                x_,
            );
            let second = rubi_rhs_int(
                &(binomial.pow(&n_) * factor * quadratic.pow(&p_ - Atom::num(1))),
                x_,
            );
            let denominator = &e__ * &ef_dg;
            rubi_star(&invariant / &denominator, first)
                    - rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 739,
        source: "Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          e*(e*f-d*g)/(c*d^2+a*e^2) \\[Star] Int[(f+g*x)^(n-1)*(a+c*x^2)^(p+1)/(d+e*x),x] +
          1/(c*d^2+a*e^2) \\[Star] Int[(f+g*x)^(n-1)*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g},x] &&
          Not[IntegerQ[n]] && Not[IntegerQ[p]] && LtQ[p,-1] && GtQ[n,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && !integerq!(n_)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let factor = &c__ * &d__ * &f__ + &a__ * &e__ * &g__ - &c__ * &ef_dg * x_;
            let first = rubi_rhs_int(
                &(binomial.pow(&n_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &linear),
                x_,
            );
            let second = rubi_rhs_int(
                &(binomial.pow(&n_ - Atom::num(1)) * factor * quadratic.pow(&p_)),
                x_,
            );
            rubi_star(&e__ * &ef_dg / &invariant, first)
                    + rubi_star(Atom::num(1) / invariant, second)
        },
    ));
}

fn push_rules_rule_740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 740,
        source: "Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[n+1/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: ["Algebraic expansion"],
        pattern: (f__ + g__ * x_).pow(n_) / ((d__ + e__ * x_) * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(&n_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let u = Atom::num(1) / ((&f__ + &g__ * x_).sqrt() * (&a__ + &c__ * x_.pow(2)).sqrt());
            let v_expr = (&f__ + &g__ * x_).pow(&n_ + Atom::num(1) / Atom::num(2)) / (&d__ + &e__ * x_);
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let rule = rubi_rule!(
        order: 741,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && (IntegerQ[p] || ILtQ[m,0] && ILtQ[n,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && (integerq!(p_) || iltq!(m_, 0) && iltq!(n_, 0))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&n_) * (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    );
    rules.push(rule.with_even_quadratic_binomial_base());
}

fn push_rules_rule_742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 742,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,d+e*x,x], R=PolynomialRemainder[(f+g*x)^n,d+e*x,x]},
          (e*R*(d+e*x)^(m+1)*(a+c*x^2)^(p+1))/((m+1)*(c*d^2+a*e^2)) +
          1/((m+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p*
             ExpandToSum[(m+1)*(c*d^2+a*e^2)*Q+c*d*R*(m+1)-c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,c,d,e,f,g,p},x] && IGtQ[n,1] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_)
                && igtq!(n_, 1)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_power = (&f__ + &g__ * x_).pow(&n_);
            let quadratic = &a__ + &c__ * x_.pow(2);
            let capital_q = rubi_polynomial_quotient(&second_power, &first_affine, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&second_power, &first_affine, x_).rubi_rhs();
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = &e__
                * &capital_r
                * first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &((&m_ + Atom::num(1)) * &invariant * capital_q
                    + &c__ * &d__ * &capital_r * (&m_ + Atom::num(1))
                    - &c__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 743,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^p*ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-
            g^n*(d+e*x)^(n-2)*(a*e^2*(m+n-1)-c*d^2*(m+n+2*p+1)-2*c*d*e*(m+n+p)*x),x],x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && IGtQ[n,1] && NeQ[m+n+2*p+1,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && igtq!(n_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let denominator = &c__ * e__.pow(&n_) * &balance;
            let direct = g__.pow(&n_)
                * first_affine.pow(&m_ + &n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &balance);
            let payload = rubi_expand_to_sum(
                &(&c__ * e__.pow(&n_) * &balance * second_affine.pow(&n_)
                    - &c__ * g__.pow(&n_) * &balance * first_affine.pow(&n_)
                    - g__.pow(&n_)
                        * first_affine.pow(&n_ - Atom::num(2))
                        * (&a__ * e__.pow(2) * (&m_ + &n_ - Atom::num(1))
                            - &c__ * d__.pow(2) * &balance
                            - Atom::num(2)
                                * &c__
                                * &d__
                                * &e__
                                * (&m_ + &n_ + &p_)
                                * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first_affine.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 744,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        // Loading the source optional definition merges its p = 1 case into
        // earlier DownValues; the installed DownValue 744 requires p_.
        optional: [c__, d__, e__, f__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: { freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&d__ + &e__ * x_).pow(&m_)
                    * (&f__ + &g__ * x_).pow(&n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, n_, p_, u_);
    let rule = rubi_rule!(
        order: 745,
        source: "Int[(d_.+e_.*u_)^m_.*(f_.+g_.*u_)^n_.*(a_+c_.*u_^2)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x,u] /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * u_).pow(m_) * (f__ + g__ * u_).pow(n_) * (a__ + c__ * u_.pow(2)).pow(p_),
        with: [a__, c__, d__, e__, f__, g__, u_, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_, p_],
        x_dep: [],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        x_linear: [u_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(u_, x_)
        },
        rhs: {
            let (_u0, u1) = linear_coefficients(&u_, x_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&d__ + &e__ * &sub_atom).pow(&m_) * (&f__ + &g__ * &sub_atom).pow(&n_) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, u_);
            rubi_star(Atom::num(1) / u1, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_) * (a__ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).sqrt() / (a__ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) / ((f__ + g__ * x_).sqrt() * (a__ + c__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(n_) * (a__ + c__ * x_.pow(2)).pow(p_) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_) * (a__ + b__ * x_.pow(2)).sqrt())
}
