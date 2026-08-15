use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1294(rules);
    push_rules_rule_1295(rules);
    push_rules_rule_1296(rules);
    push_rules_rule_1297(rules);
    push_rules_rule_1298(rules);
    push_rules_rule_1299(rules);
    push_rules_rule_1300(rules);
    push_rules_rule_1301(rules);
    push_rules_rule_1302(rules);
    push_rules_rule_1303(rules);
    push_rules_rule_1304(rules);
    push_rules_rule_1305(rules);
    push_rules_rule_1306(rules);
    push_rules_rule_1307(rules);
    push_rules_rule_1308(rules);
    push_rules_rule_1309(rules);
    push_rules_rule_1310(rules);
    push_rules_rule_1311(rules);
    push_rules_rule_1312(rules);
    push_rules_rule_1313(rules);
    push_rules_rule_1314(rules);
    push_rules_rule_1315(rules);
    push_rules_rule_1316(rules);
    push_rules_rule_1317(rules);
    push_rules_rule_1318(rules);
    push_rules_rule_1319(rules);
    push_rules_rule_1320(rules);
    push_rules_rule_1321(rules);
    push_rules_rule_1322(rules);
    push_rules_rule_1323(rules);
    push_rules_rule_1324(rules);
    push_rules_rule_1325(rules);
    push_rules_rule_1326(rules);
    push_rules_rule_1327(rules);
    push_rules_rule_1328(rules);
}

fn push_rules_rule_1294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1294,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          1/c^p \\[Star] Int[(b/2+c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,q},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, c__, d__, e__, f__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed_integrand = (&b__ / Atom::num(2) + &c__ * x_)
                .pow(Atom::num(2) * &p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1295,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          (c/f)^p \\[Star] Int[(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) &&
          (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, c__, e__, f__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && (integerq!(p_) || gtq!(&c__ / &f__, 0))
                && (!integerq!(q_)
                    || rubi_leaf_count(&second) <= rubi_leaf_count(&first))
        },
        rhs: {
            let recursive_integrand =
                (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&p_ + &q_);
            rubi_star((&c__ / &f__).pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1296,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p]) \\[Star] Int[(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, c__, e__, f__, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && !integerq!(p_)
                && !integerq!(q_)
                && !gtq!(&c__ / &f__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let prefactor = a__.pow(rubi_int_part(&p_)) * first.pow(rubi_frac_part(&p_))
                / (d__.pow(rubi_int_part(&p_)) * second.pow(rubi_frac_part(&p_)));
            rubi_star(prefactor, rubi_rhs_int(&second.pow(&p_ + &q_), x_))
        },
    ));
}

fn push_rules_rule_1297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1297,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [b__, c__, e__, f__, q_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let frac_p = rubi_frac_part(&p_);
            let prefactor = first.pow(&frac_p)
                / ((Atom::num(4) * &c__).pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * &frac_p));
            let transformed_integrand = linear.pow(Atom::num(2) * &p_) * second.pow(&q_);
            rubi_star(prefactor, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1298,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_.,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,f,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, p_, q_, x_],
        optional: [b__, c__, f__, q_],
        x_free: [a__, b__, c__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, p_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let second = &d__ + &f__ * x_.pow(2);
            let frac_p = rubi_frac_part(&p_);
            let prefactor = first.pow(&frac_p)
                / ((Atom::num(4) * &c__).pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * &frac_p));
            let transformed_integrand = linear.pow(Atom::num(2) * &p_) * second.pow(&q_);
            rubi_star(prefactor, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1299,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(b/2-r/2+c*x)^p*(b/2+r/2+c*x)^p*(d+e*x+f*x^2)^q,x],x] /;
         EqQ[p,-1] || Not[FractionalPowerFactorQ[r]]] /;
        FreeQ[{a,b,c,d,e,f},x] && ILtQ[p,0] && IntegerQ[q] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && iltq!(p_, 0)
                && integerq!(q_)
                && rubi_nice_sqrt_q(&(b__.pow(2) - Atom::num(4) * &a__ * &c__))
                && (eqq!(p_, -1) || !rubi_fractional_power_factor_q(&r))
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let integrand = (&b__ / Atom::num(2) - &r / Atom::num(2) + &c__ * x_)
                .pow(&p_)
                * (&b__ / Atom::num(2) + &r / Atom::num(2) + &c__ * x_).pow(&p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1300,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(b/2-r/2+c*x)^p*(b/2+r/2+c*x)^p*(d+f*x^2)^q,x],x] /;
         EqQ[p,-1] || Not[FractionalPowerFactorQ[r]]] /;
        FreeQ[{a,b,c,d,f},x] && ILtQ[p,0] && IntegerQ[q] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__, d__, f__], x_)
                && iltq!(p_, 0)
                && integerq!(q_)
                && rubi_nice_sqrt_q(&(b__.pow(2) - Atom::num(4) * &a__ * &c__))
                && (eqq!(p_, -1) || !rubi_fractional_power_factor_q(&r))
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let integrand = (&b__ / Atom::num(2) - &r / Atom::num(2) + &c__ * x_)
                .pow(&p_)
                * (&b__ / Atom::num(2) + &r / Atom::num(2) + &c__ * x_).pow(&p_)
                * (&d__ + &f__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1301,
        source: "Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          With[{r=Rt[-a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(-r+c*x)^p*(r+c*x)^p*(d+e*x+f*x^2)^q,x],x] /;
         EqQ[p,-1] || Not[FractionalPowerFactorQ[r]]] /;
        FreeQ[{a,c,d,e,f},x] && ILtQ[p,0] && IntegerQ[q] && NiceSqrtQ[-a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            freeq!([a__, c__, d__, e__, f__], x_)
                && iltq!(p_, 0)
                && integerq!(q_)
                && rubi_nice_sqrt_q(&(-&a__ * &c__))
                && (eqq!(p_, -1) || !rubi_fractional_power_factor_q(&r))
        },
        rhs: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            let integrand = (-&r + &c__ * x_).pow(&p_)
                * (&r + &c__ * x_).pow(&p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1302,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (b+2*c*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((b^2-4*a*c)*(p+1)) -
          (1/((b^2-4*a*c)*(p+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[2*c*d*(2*p+3)+b*e*q+(2*b*f*q+2*c*e*(2*p+q+3))*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let direct = (&b__ + Atom::num(2) * &c__ * x_)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_)
                / &denominator;
            let polynomial = simp!(
                Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3))
                    + &b__ * &e__ * &q_
                    + (Atom::num(2) * &b__ * &f__ * &q_ + Atom::num(2) * &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(3))) * x_
                    + Atom::num(2) * &c__ * &f__ * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ - Atom::num(1))
                * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1303,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
          (b+2*c*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/((b^2-4*a*c)*(p+1)) -
          (1/((b^2-4*a*c)*(p+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
              Simp[2*c*d*(2*p+3)+(2*b*f*q)*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let direct = (&b__ + Atom::num(2) * &c__ * x_)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_)
                / &denominator;
            let polynomial = simp!(
                Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3))
                    + (Atom::num(2) * &b__ * &f__ * &q_) * x_
                    + Atom::num(2) * &c__ * &f__ * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ - Atom::num(1))
                * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1304,
        source: "Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (2*c*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((-4*a*c)*(p+1)) -
          (1/((-4*a*c)*(p+1))) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[2*c*d*(2*p+3)+(2*c*e*(2*p+q+3))*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = -Atom::num(4) * &a__ * &c__ * (&p_ + Atom::num(1));
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let direct = Atom::num(2)
                * &c__
                * x_
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_)
                / &denominator;
            let polynomial = simp!(
                Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3))
                    + Atom::num(2)
                        * &c__
                        * &e__
                        * (Atom::num(2) * &p_ + &q_ + Atom::num(3))
                        * x_
                    + Atom::num(2)
                        * &c__
                        * &f__
                        * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ - Atom::num(1))
                * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1305,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (2*a*c^2*e-b^2*c*e+b^3*f+b*c*(c*d-3*a*f)+c*(2*c^2*d+b^2*f-c*(b*e+2*a*f))*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/
            ((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)) -
          (1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[2*c*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)-
                (2*c^2*d+b^2*f-c*(b*e+2*a*f))*(a*f*(p+1)-c*d*(p+2))-
                e*(b^2*c*e-2*a*c^2*e-b^3*f-b*c*(c*d-3*a*f))*(p+q+2)+
               (2*f*(2*a*c^2*e-b^2*c*e+b^3*f+b*c*(c*d-3*a*f))*(p+q+2)-(2*c^2*d+b^2*f-c*(b*e+2*a*f))*(b*f*(p+1)-c*e*(2*p+q+4)))*x+
               c*f*(2*c^2*d+b^2*f-c*(b*e+2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] &&
          NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            let delta = (&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let delta = (&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * &delta * (&p_ + Atom::num(1));
            let lead = Atom::num(2) * &a__ * c__.pow(2) * &e__
                - b__.pow(2) * &c__ * &e__
                + b__.pow(3) * &f__
                + &b__ * &c__ * (&c__ * &d__ - Atom::num(3) * &a__ * &f__);
            let tail = Atom::num(2) * c__.pow(2) * &d__
                + b__.pow(2) * &f__
                - &c__ * (&b__ * &e__ + Atom::num(2) * &a__ * &f__);
            let direct = (&lead + &c__ * &tail * x_)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                Atom::num(2) * &c__ * &delta * (&p_ + Atom::num(1))
                    - &tail * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    - &e__
                        * (b__.pow(2) * &c__ * &e__
                            - Atom::num(2) * &a__ * c__.pow(2) * &e__
                            - b__.pow(3) * &f__
                            - &b__ * &c__ * (&c__ * &d__ - Atom::num(3) * &a__ * &f__))
                        * (&p_ + &q_ + Atom::num(2))
                    + (Atom::num(2) * &f__ * &lead * (&p_ + &q_ + Atom::num(2))
                        - &tail
                            * (&b__ * &f__ * (&p_ + Atom::num(1))
                                - &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(4))))
                        * x_
                    + &c__ * &f__ * &tail * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand =
                first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1306(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1306,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
          (b^3*f+b*c*(c*d-3*a*f)+c*(2*c^2*d+b^2*f-c*(2*a*f))*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/
            ((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1)) -
          (1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
              Simp[2*c*(b^2*d*f+(c*d-a*f)^2)*(p+1)-
                (2*c^2*d+b^2*f-c*(2*a*f))*(a*f*(p+1)-c*d*(p+2))+
               (2*f*(b^3*f+b*c*(c*d-3*a*f))*(p+q+2)-(2*c^2*d+b^2*f-c*(2*a*f))*(b*f*(p+1)))*x+
               c*f*(2*c^2*d+b^2*f-c*(2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,b,c,d,f,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] &&
          Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__, q_],
        when: {
            let delta = b__.pow(2) * &d__ * &f__ + (&c__ * &d__ - &a__ * &f__).pow(2);
            freeq!([a__, b__, c__, d__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let delta = b__.pow(2) * &d__ * &f__ + (&c__ * &d__ - &a__ * &f__).pow(2);
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * &delta * (&p_ + Atom::num(1));
            let lead = b__.pow(3) * &f__ + &b__ * &c__ * (&c__ * &d__ - Atom::num(3) * &a__ * &f__);
            let tail = Atom::num(2) * c__.pow(2) * &d__ + b__.pow(2) * &f__ - &c__ * (Atom::num(2) * &a__ * &f__);
            let direct = (&lead + &c__ * &tail * x_)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                Atom::num(2) * &c__ * &delta * (&p_ + Atom::num(1))
                    - &tail * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    + (Atom::num(2) * &f__ * &lead * (&p_ + &q_ + Atom::num(2))
                        - &tail * (&b__ * &f__ * (&p_ + Atom::num(1))))
                        * x_
                    + &c__ * &f__ * &tail * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand =
                first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1307(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1307,
        source: "Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (2*a*c^2*e+c*(2*c^2*d-c*(2*a*f))*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/
            ((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1)) -
          (1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[2*c*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)-(2*c^2*d-c*(2*a*f))*(a*f*(p+1)-c*d*(p+2))-e*(-2*a*c^2*e)*(p+q+2)+
               (2*f*(2*a*c^2*e)*(p+q+2)-(2*c^2*d-c*(2*a*f))*(-c*e*(2*p+q+4)))*x+
               c*f*(2*c^2*d-c*(2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,c,d,e,f,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] &&
          Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            let delta = &a__ * &c__ * e__.pow(2) + (&c__ * &d__ - &a__ * &f__).pow(2);
            freeq!([a__, c__, d__, e__, f__, q_], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
                && !igtq!(q_, 0)
        },
        rhs: {
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let delta = &a__ * &c__ * e__.pow(2) + (&c__ * &d__ - &a__ * &f__).pow(2);
            let denominator = Atom::num(-4) * &a__ * &c__ * &delta * (&p_ + Atom::num(1));
            let lead = Atom::num(2) * &a__ * c__.pow(2) * &e__;
            let tail = Atom::num(2) * c__.pow(2) * &d__ - &c__ * (Atom::num(2) * &a__ * &f__);
            let direct = (&lead + &c__ * &tail * x_)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                Atom::num(2)
                    * &c__
                    * ((&c__ * &d__ - &a__ * &f__).pow(2) - (Atom::num(-1) * &a__ * &e__) * (&c__ * &e__))
                    * (&p_ + Atom::num(1))
                    - &tail * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    - &e__ * (Atom::num(-2) * &a__ * c__.pow(2) * &e__) * (&p_ + &q_ + Atom::num(2))
                    + (Atom::num(2)
                        * &f__
                        * (Atom::num(2) * &a__ * c__.pow(2) * &e__)
                        * (&p_ + &q_ + Atom::num(2))
                        - &tail
                            * (Atom::num(-1) * &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(4))))
                        * x_
                    + &c__ * &f__ * &tail * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand =
                first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1308(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1308,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (b*f*(3*p+2*q)-c*e*(2*p+q)+2*c*f*(p+q)*x)*(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(p+q)*(2*p+2*q+1)) -
          1/(2*f^2*(p+q)*(2*p+2*q+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p-2)*(d+e*x+f*x^2)^q*
              Simp[(b*d-a*e)*(c*e-b*f)*(1-p)*(2*p+q)-
                (p+q)*(b^2*d*f*(1-p)-a*(f*(b*e-2*a*f)*(2*p+2*q+1)+c*(2*d*f-e^2*(2*p+q))))+
                (2*(c*d-a*f)*(c*e-b*f)*(1-p)*(2*p+q)-
                  (p+q)*((b^2-4*a*c)*e*f*(1-p)+b*(c*(e^2-4*d*f)*(2*p+q)+f*(2*c*d-b*e+2*a*f)*(2*p+2*q+1))))*x+
                ((c*e-b*f)^2*(1-p)*p+c*(p+q)*(f*(b*e-2*a*f)*(4*p+2*q-1)-c*(2*d*f*(1-2*p)+e^2*(3*p+q-1))))*x^2,x],x]/;
        FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,1] &&
          NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && gtq!(p_, 1)
                && neq!(&p_ + &q_, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = Atom::num(2)
                * f__.pow(2)
                * (&p_ + &q_)
                * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let direct = (&b__ * &f__ * (Atom::num(3) * &p_ + Atom::num(2) * &q_)
                - &c__ * &e__ * (Atom::num(2) * &p_ + &q_)
                + Atom::num(2) * &c__ * &f__ * (&p_ + &q_) * x_)
                * first.pow(&p_ - Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                (&b__ * &d__ - &a__ * &e__)
                    * (&c__ * &e__ - &b__ * &f__)
                    * (Atom::num(1) - &p_)
                    * (Atom::num(2) * &p_ + &q_)
                    - (&p_ + &q_)
                        * (b__.pow(2) * &d__ * &f__ * (Atom::num(1) - &p_)
                            - &a__
                                * (&f__
                                    * (&b__ * &e__ - Atom::num(2) * &a__ * &f__)
                                    * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1))
                                    + &c__ * (Atom::num(2) * &d__ * &f__ - e__.pow(2) * (Atom::num(2) * &p_ + &q_))))
                    + (Atom::num(2)
                        * (&c__ * &d__ - &a__ * &f__)
                        * (&c__ * &e__ - &b__ * &f__)
                        * (Atom::num(1) - &p_)
                        * (Atom::num(2) * &p_ + &q_)
                        - (&p_ + &q_)
                            * ((b__.pow(2) - Atom::num(4) * &a__ * &c__)
                                * &e__
                                * &f__
                                * (Atom::num(1) - &p_)
                                + &b__
                                    * (&c__ * (e__.pow(2) - Atom::num(4) * &d__ * &f__) * (Atom::num(2) * &p_ + &q_)
                                        + &f__
                                            * (Atom::num(2) * &c__ * &d__ - &b__ * &e__ + Atom::num(2) * &a__ * &f__)
                                            * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1)))))
                        * x_
                    + ((&c__ * &e__ - &b__ * &f__).pow(2) * (Atom::num(1) - &p_) * &p_
                        + &c__
                            * (&p_ + &q_)
                            * (&f__
                                * (&b__ * &e__ - Atom::num(2) * &a__ * &f__)
                                * (Atom::num(4) * &p_ + Atom::num(2) * &q_ - Atom::num(1))
                                - &c__
                                    * (Atom::num(2) * &d__ * &f__ * (Atom::num(1) - Atom::num(2) * &p_)
                                        + e__.pow(2) * (Atom::num(3) * &p_ + &q_ - Atom::num(1)))))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(2)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1309(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1309,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
          (b*(3*p+2*q)+2*c*(p+q)*x)*(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^(q+1)/(2*f*(p+q)*(2*p+2*q+1)) -
          1/(2*f*(p+q)*(2*p+2*q+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p-2)*(d+f*x^2)^q*
              Simp[b^2*d*(p-1)*(2*p+q)-(p+q)*(b^2*d*(1-p)-2*a*(c*d-a*f*(2*p+2*q+1)))-
                (2*b*(c*d-a*f)*(1-p)*(2*p+q)-2*(p+q)*b*(2*c*d*(2*p+q)-(c*d+a*f)*(2*p+2*q+1)))*x+
                (b^2*f*p*(1-p)+2*c*(p+q)*(c*d*(2*p-1)-a*f*(4*p+2*q-1)))*x^2,x],x]/;
        FreeQ[{a,b,c,d,f,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,1] && NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 1)
                && neq!(&p_ + &q_, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator =
                Atom::num(2) * &f__ * (&p_ + &q_) * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let direct = (&b__ * (Atom::num(3) * &p_ + Atom::num(2) * &q_)
                + Atom::num(2) * &c__ * (&p_ + &q_) * x_)
                * first.pow(&p_ - Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                b__.pow(2) * &d__ * (&p_ - Atom::num(1)) * (Atom::num(2) * &p_ + &q_)
                    - (&p_ + &q_)
                        * (b__.pow(2) * &d__ * (Atom::num(1) - &p_)
                            - Atom::num(2) * &a__ * (&c__ * &d__ - &a__ * &f__ * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1))))
                    - (Atom::num(2)
                        * &b__
                        * (&c__ * &d__ - &a__ * &f__)
                        * (Atom::num(1) - &p_)
                        * (Atom::num(2) * &p_ + &q_)
                        - Atom::num(2)
                            * (&p_ + &q_)
                            * &b__
                            * (Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + &q_)
                                - (&c__ * &d__ + &a__ * &f__)
                                    * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1))))
                        * x_
                    + (b__.pow(2) * &f__ * &p_ * (Atom::num(1) - &p_)
                        + Atom::num(2)
                            * &c__
                            * (&p_ + &q_)
                            * (&c__ * &d__ * (Atom::num(2) * &p_ - Atom::num(1))
                                - &a__ * &f__ * (Atom::num(4) * &p_ + Atom::num(2) * &q_ - Atom::num(1))))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(2)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1310,
        source: "Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          -c*(e*(2*p+q)-2*f*(p+q)*x)*(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(p+q)*(2*p+2*q+1)) -
          1/(2*f^2*(p+q)*(2*p+2*q+1)) \\[Star]
            Int[(a+c*x^2)^(p-2)*(d+e*x+f*x^2)^q*
              Simp[-a*c*e^2*(1-p)*(2*p+q)+a*(p+q)*(-2*a*f^2*(2*p+2*q+1)+c*(2*d*f-e^2*(2*p+q)))+
                (2*(c*d-a*f)*(c*e)*(1-p)*(2*p+q)+4*a*c*e*f*(1-p)*(p+q))*x+
                (p*c^2*e^2*(1-p)-c*(p+q)*(2*a*f^2*(4*p+2*q-1)+c*(2*d*f*(1-2*p)+e^2*(3*p+q-1))))*x^2,x],x]/;
        FreeQ[{a,c,d,e,f,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,1] && NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, q_], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && gtq!(p_, 1)
                && neq!(&p_ + &q_, 0)
                && neq!(Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = Atom::num(2)
                * f__.pow(2)
                * (&p_ + &q_)
                * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1));
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let direct = Atom::num(-1)
                * &c__
                * (&e__ * (Atom::num(2) * &p_ + &q_) - Atom::num(2) * &f__ * (&p_ + &q_) * x_)
                * first.pow(&p_ - Atom::num(1))
                * second.pow(&q_ + Atom::num(1))
                / &denominator;
            let polynomial = simp!(
                Atom::num(-1) * &a__ * &c__ * e__.pow(2) * (Atom::num(1) - &p_) * (Atom::num(2) * &p_ + &q_)
                    + &a__
                        * (&p_ + &q_)
                        * (Atom::num(-2) * &a__ * f__.pow(2) * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(1))
                            + &c__ * (Atom::num(2) * &d__ * &f__ - e__.pow(2) * (Atom::num(2) * &p_ + &q_)))
                    + (Atom::num(2)
                        * (&c__ * &d__ - &a__ * &f__)
                        * (&c__ * &e__)
                        * (Atom::num(1) - &p_)
                        * (Atom::num(2) * &p_ + &q_)
                        + Atom::num(4) * &a__ * &c__ * &e__ * &f__ * (Atom::num(1) - &p_) * (&p_ + &q_))
                        * x_
                    + (&p_ * c__.pow(2) * e__.pow(2) * (Atom::num(1) - &p_)
                        - &c__
                            * (&p_ + &q_)
                            * (Atom::num(2) * &a__ * f__.pow(2) * (Atom::num(4) * &p_ + Atom::num(2) * &q_ - Atom::num(1))
                                + &c__
                                    * (Atom::num(2) * &d__ * &f__ * (Atom::num(1) - Atom::num(2) * &p_)
                                        + e__.pow(2) * (Atom::num(3) * &p_ + &q_ - Atom::num(1)))))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(2)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1311,
        source: "Int[1/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
          With[{q=c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2},
          1/q \\[Star] Int[(c^2*d-b*c*e+b^2*f-a*c*f-(c^2*e-b*c*f)*x)/(a+b*x+c*x^2),x] +
          1/q \\[Star] Int[(c*e^2-c*d*f-b*e*f+a*f^2+(c*e*f-b*f^2)*x)/(d+e*x+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            let q = c__.pow(2) * d__.pow(2) - &b__ * &c__ * &d__ * &e__
                + &a__ * &c__ * e__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                - &a__ * &b__ * &e__ * &f__
                + a__.pow(2) * f__.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(q, 0)
        },
        rhs: {
            let q = c__.pow(2) * d__.pow(2) - &b__ * &c__ * &d__ * &e__
                + &a__ * &c__ * e__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                - &a__ * &b__ * &e__ * &f__
                + a__.pow(2) * f__.pow(2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_numerator = c__.pow(2) * &d__
                - &b__ * &c__ * &e__
                + b__.pow(2) * &f__
                - &a__ * &c__ * &f__
                - (&c__ * &c__ * &e__ - &b__ * &c__ * &f__) * x_;
            let second_numerator = &c__ * e__.pow(2) - &c__ * &d__ * &f__ - &b__ * &e__ * &f__
                + &a__ * f__.pow(2)
                + (&c__ * &e__ * &f__ - &b__ * f__.pow(2)) * x_;
            let first_integrand = first_numerator / first;
            let second_integrand = second_numerator / second;

            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 1312,
        source: "Int[1/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
          With[{q=c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2},
          1/q \\[Star] Int[(c^2*d+b^2*f-a*c*f+b*c*f*x)/(a+b*x+c*x^2),x] -
          1/q \\[Star] Int[(c*d*f-a*f^2+b*f^2*x)/(d+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2))),
        with: [a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            let q = c__.pow(2) * d__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                + a__.pow(2) * f__.pow(2);
            freeq!([a__, b__, c__, d__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(q, 0)
        },
        rhs: {
            let q = c__.pow(2) * d__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                + a__.pow(2) * f__.pow(2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let first_numerator =
                c__.pow(2) * &d__ + b__.pow(2) * &f__ - &a__ * &c__ * &f__ + &b__ * &c__ * &f__ * x_;
            let second_numerator = &c__ * &d__ * &f__ - &a__ * f__.pow(2) + &b__ * f__.pow(2) * x_;
            let first_integrand = first_numerator / first;
            let second_integrand = second_numerator / second;

            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1313,
        source: "Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -2*e \\[Star] Subst[Int[1/(e*(b*e-4*a*f)-(b*d-a*e)*x^2),x],x,(e+2*f*x)/Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0]",
        desc: "Integration by substitution",
        refs: ["G&R 2.252.3b"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&c__ * &e__ - &b__ * &f__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / (&e__ * (&b__ * &e__ - Atom::num(4) * &a__ * &f__) - (&b__ * &d__ - &a__ * &e__) * sub.pow(2));
            let substitution = (&e__ + Atom::num(2) * &f__ * x_) / (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(-2) * &e__, rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub_symbol),
                    sub_symbol,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1314,
        source: "Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
          2*c/q \\[Star] Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[c*e-b*f,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(discriminant, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(&c__ * &e__ - &b__ * &f__, 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let second = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = Atom::num(1) / ((&b__ - &q + Atom::num(2) * &c__ * x_) * &second);
            let second_integrand = Atom::num(1) / ((&b__ + &q + Atom::num(2) * &c__ * x_) * second);
            rubi_star(Atom::num(2) * &c__ / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(2) * &c__ / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1316,
        source: "Int[1/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          1/2 \\[Star] Int[1/((a-Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] +
          1/2 \\[Star] Int[1/((a+Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] /;
        FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0] && PosQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, x_],
        optional: [c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && posq!(-&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let second = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = Atom::num(1) / ((&a__ - &q * x_) * &second);
            let second_integrand = Atom::num(1) / ((&a__ + &q * x_) * second);
            rubi_star(Atom::num(1) / Atom::num(2), rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / Atom::num(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 1315,
        source: "Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
          2*c/q \\[Star] Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, f__], x_)
                && neq!(discriminant, 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let second = (&d__ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = Atom::num(1) / ((&b__ - &q + Atom::num(2) * &c__ * x_) * &second);
            let second_integrand = Atom::num(1) / ((&b__ + &q + Atom::num(2) * &c__ * x_) * second);
            rubi_star(Atom::num(2) * &c__ / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(2) * &c__ / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1317,
        source: "Int[1/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),2]},
          1/(2*q) \\[Star] Int[(c*d-a*f+q+(c*e-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] -
          1/(2*q) \\[Star] Int[(c*d-a*f-q+(c*e-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[c*e-b*f,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(&c__ * &e__ - &b__ * &f__, 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(
                &((&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__)),
                2,
            );
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand =
                (&c__ * &d__ - &a__ * &f__ + &q + (&c__ * &e__ - &b__ * &f__) * x_) / (&first * &second);
            let second_integrand =
                (&c__ * &d__ - &a__ * &f__ - &q + (&c__ * &e__ - &b__ * &f__) * x_) / (first * second);
            rubi_star(Atom::num(1) / (Atom::num(2) * &q), rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / (Atom::num(2) * q), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1318,
        source: "Int[1/((a_.+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2+a*c*e^2,2]},
          1/(2*q) \\[Star] Int[(c*d-a*f+q+c*e*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] -
          1/(2*q) \\[Star] Int[(c*d-a*f-q+c*e*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0] && NegQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, x_],
        optional: [a__, c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && negq!(-&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&((&c__ * &d__ - &a__ * &f__).pow(2) + &a__ * &c__ * e__.pow(2)), 2);
            let first = &a__ + &c__ * x_.pow(2);
            let second = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = (&c__ * &d__ - &a__ * &f__ + &q + &c__ * &e__ * x_) / (&first * &second);
            let second_integrand = (&c__ * &d__ - &a__ * &f__ - &q + &c__ * &e__ * x_) / (first * second);
            rubi_star(Atom::num(1) / (Atom::num(2) * &q), rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / (Atom::num(2) * q), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 1319,
        source: "Int[1/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2+b^2*d*f,2]},
          1/(2*q) \\[Star] Int[(c*d-a*f+q+(-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] -
          1/(2*q) \\[Star] Int[(c*d-a*f-q+(-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, x_],
        optional: [a__, b__, c__, d__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&((&c__ * &d__ - &a__ * &f__).pow(2) + b__.pow(2) * &d__ * &f__), 2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = (&d__ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = (&c__ * &d__ - &a__ * &f__ + &q + (Atom::num(-1) * &b__ * &f__) * x_)
                / (&first * &second);
            let second_integrand = (&c__ * &d__ - &a__ * &f__ - &q + (Atom::num(-1) * &b__ * &f__) * x_)
                / (first * second);
            rubi_star(Atom::num(1) / (Atom::num(2) * &q), rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / (Atom::num(2) * q), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1320,
        source: "Int[Sqrt[a_+b_.*x_+c_.*x_^2]/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
          c/f \\[Star] Int[1/Sqrt[a+b*x+c*x^2],x] -
          1/f \\[Star] Int[(c*d-a*f+(c*e-b*f)*x)/(Sqrt[a+b*x+c*x^2]*(d+e*x+f*x^2)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() / (d__ + e__ * x_ + f__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_integrand = Atom::num(1) / first.sqrt();
            let second_integrand =
                (&c__ * &d__ - &a__ * &f__ + (&c__ * &e__ - &b__ * &f__) * x_) / (first.sqrt() * second);

            rubi_star(&c__ / &f__, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / f__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 1321,
        source: "Int[Sqrt[a_+b_.*x_+c_.*x_^2]/(d_+f_.*x_^2),x_Symbol] :=
          c/f \\[Star] Int[1/Sqrt[a+b*x+c*x^2],x] -
          1/f \\[Star] Int[(c*d-a*f-b*f*x)/(Sqrt[a+b*x+c*x^2]*(d+f*x^2)),x] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() / (d__ + f__ * x_.pow(2)),
        with: [a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let first_integrand = Atom::num(1) / first.sqrt();
            let second_integrand = (&c__ * &d__ - &a__ * &f__ - &b__ * &f__ * x_) / (first.sqrt() * second);

            rubi_star(&c__ / &f__, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / f__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1322,
        source: "Int[Sqrt[a_+c_.*x_^2]/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
          c/f \\[Star] Int[1/Sqrt[a+c*x^2],x] -
          1/f \\[Star] Int[(c*d-a*f+c*e*x)/(Sqrt[a+c*x^2]*(d+e*x+f*x^2)),x] /;
        FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + c__ * x_.pow(2)).sqrt() / (d__ + e__ * x_ + f__ * x_.pow(2)),
        with: [a__, c__, d__, e__, f__, x_],
        optional: [c__, e__, f__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
        },
        rhs: {
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_integrand = Atom::num(1) / first.sqrt();
            let second_integrand = (&c__ * &d__ - &a__ * &f__ + &c__ * &e__ * x_) / (first.sqrt() * second);

            rubi_star(&c__ / &f__, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / f__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1323,
        source: "Int[1/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]/Sqrt[a+b*x+c*x^2] \\[Star] Int[1/(Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let linear_1 = &b__ + &r + Atom::num(2) * &c__ * x_;
            let linear_2 = Atom::num(2) * &a__ + (&b__ + &r) * x_;
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let recursive_integrand = Atom::num(1) / (linear_1.sqrt() * linear_2.sqrt() * second.sqrt());
            rubi_star(linear_1.sqrt() * linear_2.sqrt() / first.sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 1324,
        source: "Int[1/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]/Sqrt[a+b*x+c*x^2] \\[Star] Int[1/(Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() * (d__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, f__, x_],
        optional: [b__, c__, f__],
        x_free: [a__, b__, c__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, f__], x_) && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let linear_1 = &b__ + &r + Atom::num(2) * &c__ * x_;
            let linear_2 = Atom::num(2) * &a__ + (&b__ + &r) * x_;
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let recursive_integrand = Atom::num(1) / (linear_1.sqrt() * linear_2.sqrt() * second.sqrt());
            rubi_star(linear_1.sqrt() * linear_2.sqrt() / first.sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1325,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          Unintegrable[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_)
                    * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1326,
        source: "Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          Unintegrable[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,c,d,e,f,p,q},x] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, p_, q_, x_],
        optional: [c__, d__, e__, f__],
        x_free: [a__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_, q_], x_)
                && !igtq!(p_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&a__ + &c__ * x_.pow(2)).pow(&p_)
                    * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, p_, q_, u__);
    rules.push(rubi_rule!(
        order: 1327,
        source: "Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_),
        with: [a__, b__, c__, d__, e__, f__, p_, q_, u__, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_, q_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_) * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / coefficient, rubi_subst(&rubi_rhs_int(&transformed_integrand, sub), sub, u__))
        },
    ));
}

fn push_rules_rule_1328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, p_, q_, u__);
    rules.push(rubi_rule!(
        order: 1328,
        source: "Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
        FreeQ[{a,c,d,e,f,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_),
        with: [a__, c__, d__, e__, f__, p_, q_, u__, x_],
        optional: [a__, c__, d__, e__, f__, p_, q_],
        x_dep: [],
        x_free: [a__, c__, d__, e__, f__, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &c__ * sub_atom.pow(2)).pow(&p_) * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / coefficient, rubi_subst(&rubi_rhs_int(&transformed_integrand, sub), sub, u__))
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
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (d__ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + c__ * x_.pow(2)).pow(p_) * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt())
}
