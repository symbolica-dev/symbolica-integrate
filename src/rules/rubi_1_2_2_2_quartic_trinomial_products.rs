use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1419(rules);
    push_rules_rule_1420(rules);
    push_rules_rule_1421(rules);
    push_rules_rule_1422(rules);
    push_rules_rule_1423(rules);
    push_rules_rule_1424(rules);
    push_rules_rule_1425(rules);
    push_rules_rule_1426(rules);
    push_rules_rule_1427(rules);
    push_rules_rule_1428(rules);
    push_rules_rule_1429(rules);
    push_rules_rule_1430(rules);
    push_rules_rule_1431(rules);
    push_rules_rule_1432(rules);
    push_rules_rule_1433(rules);
    push_rules_rule_1434(rules);
    push_rules_rule_1435(rules);
    push_rules_rule_1436(rules);
    push_rules_rule_1437(rules);
    push_rules_rule_1438(rules);
    push_rules_rule_1439(rules);
    push_rules_rule_1440(rules);
    push_rules_rule_1441(rules);
    push_rules_rule_1442(rules);
    push_rules_rule_1443(rules);
    push_rules_rule_1444(rules);
    push_rules_rule_1445(rules);
    push_rules_rule_1446(rules);
    push_rules_rule_1447(rules);
    push_rules_rule_1448(rules);
    push_rules_rule_1449(rules);
    push_rules_rule_1450(rules);
    push_rules_rule_1451(rules);
    push_rules_rule_1452(rules);
    push_rules_rule_1453(rules);
    push_rules_rule_1454(rules);
    push_rules_rule_1455(rules);
    push_rules_rule_1456(rules);
    push_rules_rule_1457(rules);
    push_rules_rule_1458(rules);
    push_rules_rule_1459(rules);
    push_rules_rule_1460(rules);
    push_rules_rule_1461(rules);
    push_rules_rule_1462(rules);
}

fn push_rules_rule_1419(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1419,
        source: "Int[(d_.*x_)^m_.*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          1/d^(2*p) \\[Star] Int[(d*x)^(m+2*p)*(b+c*x^2)^p,x] /;
        FreeQ[{b,c,d,m},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__, m_],
        x_free: [b__, c__, d__, m_],
        when: { freeq!([b__, c__, d__, m_], x_) && integerq!(p_) },
        rhs: {
            let recursive_integrand = (&d__ * x_).pow(&m_ + Atom::num(2) * &p_)
                * (&b__ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star(Atom::num(1) / d__.pow(Atom::num(2) * &p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1420(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1420,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d^3*(d*x)^(m-3)*(b*x^2+c*x^4)^(p+1)/(2*c*(p+1)) /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && EqQ[m+2*p-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && eqq!(&m_ + Atom::num(2) * &p_ - 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_simp(&(d__.pow(3) * (&d__ * x_).pow(&m_ - 3) * binomial.pow(&p_ + 1)
                    / (Atom::num(2) * &c__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_1421(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1421,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d^3*(d*x)^(m-3)*(b*x^2+c*x^4)^(p+1)/(c*(m+4*p+1)) -
          b*d^2*(m+2*p-1)/(c*(m+4*p+1)) \\[Star] Int[(d*x)^(m-2)*(b*x^2+c*x^4)^p,x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && IGtQ[Simplify[(m+2*p-1)/2],0] && NeQ[m+4*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            let shifted = rubi_simplify(&((&m_ + Atom::num(2) * &p_ - 1) / 2));
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && igtq!(shifted, 0)
                && neq!(&m_ + Atom::num(4) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * (&m_ + Atom::num(4) * &p_ + 1);
            let direct = d__.pow(3)
                * (&d__ * x_).pow(&m_ - 3)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = &b__ * d__.pow(2) * (&m_ + Atom::num(2) * &p_ - 1)
                / denominator;
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - 2) * binomial.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1422(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1422,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -d*(d*x)^(m-1)*(b*x^2+c*x^4)^(p+1)/(2*b*(p+1)) /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && EqQ[m+4*p+3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && eqq!(&m_ + Atom::num(4) * &p_ + 3, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_simp(&(-&d__ * (&d__ * x_).pow(&m_ - 1) * binomial.pow(&p_ + 1)
                    / (Atom::num(2) * &b__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_1423(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1423,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d*(d*x)^(m-1)*(b*x^2+c*x^4)^(p+1)/(b*(m+2*p+1)) -
          c*(m+4*p+3)/(b*d^2*(m+2*p+1)) \\[Star] Int[(d*x)^(m+2)*(b*x^2+c*x^4)^p,x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && ILtQ[Simplify[(m+4*p+3)/2],0] && NeQ[m+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            let shifted = rubi_simplify(&((&m_ + Atom::num(4) * &p_ + 3) / 2));
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && iltq!(shifted, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &b__ * (&m_ + Atom::num(2) * &p_ + 1);
            let direct = &d__
                * (&d__ * x_).pow(&m_ - 1)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = &c__ * (&m_ + Atom::num(4) * &p_ + 3)
                / (d__.pow(2) * denominator);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + 2) * binomial.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1424(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1424,
        source: "Int[x_^m_.*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{b,c,m,p},x] && Not[IntegerQ[p]] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [b__, c__, m_, p_],
        when: {
            freeq!([b__, c__, m_, p_], x_)
                && !integerq!(p_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let inner_integrand = sub_atom.pow((&m_ - 1) / 2)
                * (&b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&inner_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_1425(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1425,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (d*x)^(m+1)*(b*x^2+c*x^4)^p/(d*(m+2*p+1)) -
          2*c*p/(d^4*(m+2*p+1)) \\[Star] Int[(d*x)^(m+4)*(b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && GtQ[p,0] && LtQ[m+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && ltq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let shifted = &m_ + Atom::num(2) * &p_ + 1;
            let direct = (&d__ * x_).pow(&m_ + 1) * binomial.pow(&p_)
                / (&d__ * &shifted);
            let coefficient = Atom::num(2) * &c__ * &p_ / (d__.pow(4) * shifted);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + 4) * binomial.pow(&p_ - 1);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1426(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1426,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (d*x)^(m+1)*(b*x^2+c*x^4)^p/(d*(m+4*p+1)) +
          2*b*p/(d^2*(m+4*p+1)) \\[Star] Int[(d*x)^(m+2)*(b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && GtQ[p,0] && NeQ[m+4*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(4) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let shifted = &m_ + Atom::num(4) * &p_ + 1;
            let direct = (&d__ * x_).pow(&m_ + 1) * binomial.pow(&p_)
                / (&d__ * &shifted);
            let coefficient = Atom::num(2) * &b__ * &p_ / (d__.pow(2) * shifted);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + 2) * binomial.pow(&p_ - 1);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1427(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1427,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d^3*(d*x)^(m-3)*(b*x^2+c*x^4)^(p+1)/(2*c*(p+1)) -
          d^4*(m+2*p-1)/(2*c*(p+1)) \\[Star] Int[(d*x)^(m-4)*(b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && LtQ[p,-1] && GtQ[m+2*p+1,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && gtq!(&m_ + Atom::num(2) * &p_ + 1, 2)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &c__ * (&p_ + 1);
            let direct = d__.pow(3)
                * (&d__ * x_).pow(&m_ - 3)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = d__.pow(4) * (&m_ + Atom::num(2) * &p_ - 1)
                / denominator;
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - 4) * binomial.pow(&p_ + 1);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1428(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1428,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -d*(d*x)^(m-1)*(b*x^2+c*x^4)^(p+1)/(2*b*(p+1)) +
          d^2*(m+4*p+3)/(2*b*(p+1)) \\[Star] Int[(d*x)^(m-2)*(b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && ltq!(p_, -1)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &b__ * (&p_ + 1);
            let direct = -&d__
                * (&d__ * x_).pow(&m_ - 1)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = d__.pow(2) * (&m_ + Atom::num(4) * &p_ + 3)
                / denominator;
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - 2) * binomial.pow(&p_ + 1);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1429(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1429,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d^3*(d*x)^(m-3)*(b*x^2+c*x^4)^(p+1)/(c*(m+4*p+1)) -
          b*d^2*(m+2*p-1)/(c*(m+4*p+1)) \\[Star] Int[(d*x)^(m-2)*(b*x^2+c*x^4)^p,x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && GtQ[m+2*p-1,0] && NeQ[m+4*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && gtq!(&m_ + Atom::num(2) * &p_ - 1, 0)
                && neq!(&m_ + Atom::num(4) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * (&m_ + Atom::num(4) * &p_ + 1);
            let direct = d__.pow(3)
                * (&d__ * x_).pow(&m_ - 3)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = &b__ * d__.pow(2) * (&m_ + Atom::num(2) * &p_ - 1)
                / denominator;
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - 2) * binomial.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1430(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1430,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d*(d*x)^(m-1)*(b*x^2+c*x^4)^(p+1)/(b*(m+2*p+1)) -
          c*(m+4*p+3)/(b*d^2*(m+2*p+1)) \\[Star] Int[(d*x)^(m+2)*(b*x^2+c*x^4)^p,x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] && LtQ[m+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: {
            freeq!([b__, c__, d__, m_, p_], x_)
                && !integerq!(p_)
                && ltq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &b__ * (&m_ + Atom::num(2) * &p_ + 1);
            let direct = &d__
                * (&d__ * x_).pow(&m_ - 1)
                * binomial.pow(&p_ + 1)
                / &denominator;
            let coefficient = &c__ * (&m_ + Atom::num(4) * &p_ + 3)
                / (d__.pow(2) * denominator);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + 2) * binomial.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1431(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1431,
        source: "Int[(d_.*x_)^m_*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (b*x^2+c*x^4)^p/((d*x)^(2*p)*(b+c*x^2)^p) \\[Star] Int[(d*x)^(m+2*p)*(b+c*x^2)^p,x] /;
        FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [b__, c__, d__, m_, p_],
        when: { freeq!([b__, c__, d__, m_, p_], x_) && !integerq!(p_) },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let normalized = &b__ + &c__ * x_.pow(2);
            let factor = binomial.pow(&p_)
                / ((&d__ * x_).pow(Atom::num(2) * &p_) * normalized.pow(&p_));
            let recursive_integrand = (&d__ * x_).pow(&m_ + Atom::num(2) * &p_)
                * normalized.pow(&p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1432(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1432,
        source: "Int[x_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          1/2 \\[Star] Subst[Int[(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,p},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let inner_integrand =
                (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&inner_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_1433(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1433,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d*x)^m*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && (EqQ[p,1] || Not[IntegerQ[(m+1)/2]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [d__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1)
                    || !integerq!((&m_ + Atom::num(1)) / Atom::num(2)))
        },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1434(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1434,
        source: "Int[x_^m_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,p},x] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, p_],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let inner_integrand = sub_atom.pow((&m_ - Atom::num(1)) / Atom::num(2))
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&inner_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_1435(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1435,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/d \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(2*k)/d^2+c*x^(4*k)/d^4)^p,x],x,(d*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [d__, b__, c__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rational_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&k * (&m_ + Atom::num(1))).expand() - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(Atom::num(2) * &k) / d__.pow(2)
                    + &c__ * sub_atom.pow(Atom::num(4) * &k) / d__.pow(4))
                .pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                (&d__ * x_).pow(Atom::num(1) / &k),
            );
            rubi_star(&k / &d__, substituted)
        },
    ));
}

fn push_rules_rule_1436(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1436,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d*(d*x)^(m-1)*(a+b*x^2+c*x^4)^p*(2*b*p+c*(m+4*p-1)*x^2)/(c*(m+4*p+1)*(m+4*p-1)) -
          2*p*d^2/(c*(m+4*p+1)*(m+4*p-1)) \\[Star]
            Int[(d*x)^(m-2)*(a+b*x^2+c*x^4)^(p-1)*Simp[a*b*(m-1)-(2*a*c*(m+4*p-1)-b^2*(m+2*p-1))*x^2,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let denominator = &c__
                * (&m_ + Atom::num(4) * &p_ + Atom::num(1))
                * (&m_ + Atom::num(4) * &p_ - Atom::num(1));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = &d__
                * (&d__ * x_).pow(&m_ - Atom::num(1))
                * quartic.pow(&p_)
                * (Atom::num(2) * &b__ * &p_
                    + &c__ * (&m_ + Atom::num(4) * &p_ - Atom::num(1)) * x_.pow(2))
                / &denominator;
            let recursive_simp = rubi_simp(
                &(&a__ * &b__ * (&m_ - Atom::num(1))
                    - (Atom::num(2) * &a__ * &c__ * (&m_ + Atom::num(4) * &p_ - Atom::num(1))
                        - b__.pow(2) * (&m_ + Atom::num(2) * &p_ - Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&d__ * x_).pow(&m_ - Atom::num(2))
                * quartic.pow(&p_ - Atom::num(1))
                * recursive_simp;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2) * &p_ * d__.pow(2) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1437(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1437,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^2+c*x^4)^p/(d*(m+1)) -
          2*p/(d^2*(m+1)) \\[Star] Int[(d*x)^(m+2)*(b+2*c*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct_denominator = &d__ * (&m_ + Atom::num(1));
            let recursive_integrand = (&d__ * x_).pow(&m_ + Atom::num(2))
                * (&b__ + Atom::num(2) * &c__ * x_.pow(2))
                * quartic.pow(&p_ - Atom::num(1));
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1)) * quartic.pow(&p_) / direct_denominator), x_)
                    - rubi_star(Atom::num(2) * &p_ / (d__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1438(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1438,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^2+c*x^4)^p/(d*(m+4*p+1)) +
          2*p/(m+4*p+1) \\[Star] Int[(d*x)^m*(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[m+4*p+1,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(1), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &m_ + Atom::num(4) * &p_ + Atom::num(1);
            let recursive_integrand = (&d__ * x_).pow(&m_)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(2))
                * quartic.pow(&p_ - Atom::num(1));
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1)) * quartic.pow(&p_)
                    / (&d__ * &denominator)), x_)
                    + rubi_star(Atom::num(2) * &p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1439(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1439,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d*(d*x)^(m-1)*(b+2*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*(p+1)*(b^2-4*a*c)) -
          d^2/(2*(p+1)*(b^2-4*a*c)) \\[Star] Int[(d*x)^(m-2)*(b*(m-1)+2*c*(m+4*p+5)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,1] && LeQ[m,3] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && leq!(m_, 3)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * (&p_ + Atom::num(1)) * &discriminant;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = &d__
                * (&d__ * x_).pow(&m_ - Atom::num(1))
                * (&b__ + Atom::num(2) * &c__ * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = (&d__ * x_).pow(&m_ - Atom::num(2))
                * (&b__ * (&m_ - Atom::num(1)) + Atom::num(2) * &c__ * (&m_ + Atom::num(4) * &p_ + Atom::num(5)) * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_)
                    - rubi_star(d__.pow(2) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1440(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1440,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -d^3*(d*x)^(m-3)*(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*(p+1)*(b^2-4*a*c)) +
          d^4/(2*(p+1)*(b^2-4*a*c)) \\[Star] Int[(d*x)^(m-4)*(2*a*(m-3)+b*(m+4*p+3)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,3] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 3)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * (&p_ + Atom::num(1)) * &discriminant;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = -d__.pow(3)
                * (&d__ * x_).pow(&m_ - Atom::num(3))
                * (Atom::num(2) * &a__ + &b__ * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = (&d__ * x_).pow(&m_ - Atom::num(4))
                * (Atom::num(2) * &a__ * (&m_ - Atom::num(3)) + &b__ * (&m_ + Atom::num(4) * &p_ + Atom::num(3)) * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_)
                    + rubi_star(d__.pow(4) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1441(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1441,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*d*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d*x)^m*(a+b*x^2+c*x^4)^(p+1)*Simp[b^2*(m+2*p+3)-2*a*c*(m+4*p+5)+b*c*(m+4*p+7)*x^2,x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let recursive_denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;
            let direct_denominator = &d__ * &recursive_denominator;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = -(&d__ * x_).pow(&m_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(2))
                * quartic.pow(&p_ + Atom::num(1))
                / &direct_denominator;
            let recursive_simp = rubi_simp(
                &(b__.pow(2) * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                    - Atom::num(2) * &a__ * &c__ * (&m_ + Atom::num(4) * &p_ + Atom::num(5))
                    + &b__ * &c__ * (&m_ + Atom::num(4) * &p_ + Atom::num(7)) * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&d__ * x_).pow(&m_)
                * quartic.pow(&p_ + Atom::num(1))
                * recursive_simp;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1442(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1442,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d^3*(d*x)^(m-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(m+4*p+1)) -
          d^4/(c*(m+4*p+1)) \\[Star]
            Int[(d*x)^(m-4)*Simp[a*(m-3)+b*(m+2*p-1)*x^2,x]*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && GtQ[m,3] && NeQ[m+4*p+1,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(m_, 3)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(1), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let denominator = &c__ * (&m_ + Atom::num(4) * &p_ + Atom::num(1));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = d__.pow(3)
                * (&d__ * x_).pow(&m_ - Atom::num(3))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_simp = rubi_simp(
                &(&a__ * (&m_ - Atom::num(3)) + &b__ * (&m_ + Atom::num(2) * &p_ - Atom::num(1)) * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&d__ * x_).pow(&m_ - Atom::num(4))
                * recursive_simp
                * quartic.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(d__.pow(4) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1443(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1443,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*d*(m+1)) -
          1/(a*d^2*(m+1)) \\[Star] Int[(d*x)^(m+2)*(b*(m+2*p+3)+c*(m+4*p+5)*x^2)*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 3b with A=1 and B=0",
        refs: ["G&R 2.160.1"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let direct_denominator = &a__ * &d__ * (&m_ + Atom::num(1));
            let recursive_denominator = &a__ * d__.pow(2) * (&m_ + Atom::num(1));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand = (&d__ * x_).pow(&m_ + Atom::num(2))
                * (&b__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) + &c__ * (&m_ + Atom::num(4) * &p_ + Atom::num(5)) * x_.pow(2))
                * quartic.pow(&p_);
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1)) * quartic.pow(&p_ + Atom::num(1)) / direct_denominator), x_)
                    - rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1444(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 1444,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          (d*x)^(m+1)/(a*d*(m+1)) -
          1/(a*d^2) \\[Star] Int[(d*x)^(m+2)*(b+c*x^2)/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.176, CRC 123"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let direct_denominator = &a__ * &d__ * (&m_ + Atom::num(1));
            let recursive_denominator = &a__ * d__.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + Atom::num(2)) * (&b__ + &c__ * x_.pow(2)) / quartic;
            rubi_simp(&((&d__ * x_).pow(&m_ + Atom::num(1)) / direct_denominator), x_)
                    - rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1445(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 1445,
        source: "Int[x_^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[PolynomialDivide[x^m,(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[m,5]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(m_, 5)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let divided = rubi_polynomial_divide(x_.pow(&m_), &quartic, x_).rubi_rhs();
            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_1446(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 1446,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          d^3*(d*x)^(m-3)/(c*(m-3)) - d^4/c \\[Star] Int[(d*x)^(m-4)*(a+b*x^2)/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[m,3]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.174.1, CRC 119"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(m_, 3)
        },
        rhs: {
            let direct_denominator = &c__ * (&m_ - Atom::num(3));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - Atom::num(4)) * (&a__ + &b__ * x_.pow(2)) / quartic;
            rubi_simp(&(d__.pow(3) * (&d__ * x_).pow(&m_ - Atom::num(3)) / direct_denominator), x_)
                    - rubi_star(d__.pow(4) / &c__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1447(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1447,
        source: "Int[x_^2/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
          With[{q=Rt[a/c,2]},
          1/2 \\[Star] Int[(q+x^2)/(a+b*x^2+c*x^4),x] - 1/2 \\[Star] Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
        FreeQ[{a,b,c},x] && LtQ[b^2-4*a*c,0] && PosQ[a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(2) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && ltq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&((&q + x_.pow(2)) / &quartic), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&((&q - x_.pow(2)) / quartic), x_))
        },
    ));
}

fn push_rules_rule_1448(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 1448,
        source: "Int[x_^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*r) \\[Star] Int[x^(m-3)*(q+r*x)/(q+r*x+x^2),x] -
          1/(2*c*r) \\[Star] Int[x^(m-3)*(q-r*x)/(q-r*x+x^2),x]]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GeQ[m,3] && LtQ[m,4] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && geq!(m_, 3)
                && ltq!(m_, 4)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let denominator = Atom::num(2) * &c__ * &r;
            let first_integrand = x_.pow(&m_ - Atom::num(3)) * (&q + &r * x_)
                / (&q + &r * x_ + x_.pow(2));
            let second_integrand = x_.pow(&m_ - Atom::num(3)) * (&q - &r * x_)
                / (&q - &r * x_ + x_.pow(2));
            let coefficient = Atom::num(1) / denominator;
            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1449(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 1449,
        source: "Int[x_^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*r) \\[Star] Int[x^(m-1)/(q-r*x+x^2),x] - 1/(2*c*r) \\[Star] Int[x^(m-1)/(q+r*x+x^2),x]]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GeQ[m,1] && LtQ[m,3] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && geq!(m_, 1)
                && ltq!(m_, 3)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let denominator = Atom::num(2) * &c__ * &r;
            let first_integrand =
                x_.pow(&m_ - Atom::num(1)) / (&q - &r * x_ + x_.pow(2));
            let second_integrand =
                x_.pow(&m_ - Atom::num(1)) / (&q + &r * x_ + x_.pow(2));
            let coefficient = Atom::num(1) / denominator;
            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1450(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 1450,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          d^2/2*(b/q+1) \\[Star] Int[(d*x)^(m-2)/(b/2+q/2+c*x^2),x] -
          d^2/2*(b/q-1) \\[Star] Int[(d*x)^(m-2)/(b/2-q/2+c*x^2),x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GeQ[m,2]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a & G&R 2.161.3"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [d__, b__, c__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && geq!(m_, 2)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand = (&d__ * x_).pow(&m_ - Atom::num(2))
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand = (&d__ * x_).pow(&m_ - Atom::num(2))
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            rubi_star(d__.pow(2) / Atom::num(2) * (&b__ / &q + Atom::num(1)), rubi_rhs_int(&first_integrand, x_)) - rubi_star(d__.pow(2) / Atom::num(2) * (&b__ / &q - Atom::num(1)), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1451(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 1451,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          c/q \\[Star] Int[(d*x)^m/(b/2-q/2+c*x^2),x] - c/q \\[Star] Int[(d*x)^m/(b/2+q/2+c*x^2),x]] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand = (&d__ * x_).pow(&m_)
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand = (&d__ * x_).pow(&m_)
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            rubi_star(&c__ / &q, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&c__ / &q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1452(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1452,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*Sqrt[-c] \\[Star] Int[x^2/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let transformed_integrand = x_.pow(2)
                / ((&b__ + &q + Atom::num(2) * &c__ * x_.pow(2)).sqrt()
                    * (-&b__ + &q - Atom::num(2) * &c__ * x_.pow(2)).sqrt());
            rubi_star(Atom::num(2) * (-&c__).sqrt(), rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1453(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1453,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,2]},
          1/q \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(&c__ / &a__, 0)
                && ltq!(&b__ / &a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) - rubi_star(Atom::num(1) / &q, rubi_rhs_int(
                        &((Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1454(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1454,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(b-q)/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c) \\[Star] Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__;
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(-(&b__ - &q) / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(
                        &((&b__ - &q + Atom::num(2) * &c__ * x_.pow(2))
                            / quartic.sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1455(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1455,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) -
          Rt[(b+q)/(2*a),2]*(2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
            EllipticE[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
         PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;

            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&b_plus_q / &a__)
                && !(posq!(&b_minus_q / &a__)
                    && rubi_simpler_sqrt_q(
                        &(&b_minus_q / (Atom::num(2) * &a__)),
                        &(&b_plus_q / (Atom::num(2) * &a__)),
                    ))
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let denominator = Atom::num(2)
                * &c__
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).sqrt();
            let rt = rubi_rt(&(&b_plus_q / (Atom::num(2) * &a__)), 2);
            let first = x_ * (&b_plus_q + Atom::num(2) * &c__ * x_.pow(2))
                / &denominator;
            let second =
                &rt
                    * (Atom::num(2) * &a__ + &b_plus_q * x_.pow(2))
                    * ((Atom::num(2) * &a__ + &b_minus_q * x_.pow(2))
                        / (Atom::num(2) * &a__ + &b_plus_q * x_.pow(2)))
                    .sqrt()
                    * rubi_elliptic_e(
                        (&rt * x_).atan(),
                        Atom::num(2) * &q / &b_plus_q,
                    )
                    / denominator;

            rubi_simp(&(first), x_) - second
        },
    ));
}

fn push_rules_rule_1456(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1456,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          x*(b-q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) -
          Rt[(b-q)/(2*a),2]*(2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
            EllipticE[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
         PosQ[(b-q)/a]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.153.1-"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;

            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&b_minus_q / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let denominator = Atom::num(2)
                * &c__
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).sqrt();
            let rt = rubi_rt(&(&b_minus_q / (Atom::num(2) * &a__)), 2);
            let first = x_ * (&b_minus_q + Atom::num(2) * &c__ * x_.pow(2))
                / &denominator;
            let second =
                &rt
                    * (Atom::num(2) * &a__ + &b_minus_q * x_.pow(2))
                    * ((Atom::num(2) * &a__ + &b_plus_q * x_.pow(2))
                        / (Atom::num(2) * &a__ + &b_minus_q * x_.pow(2)))
                    .sqrt()
                    * rubi_elliptic_e(
                        (&rt * x_).atan(),
                        -(Atom::num(2) * &q) / &b_minus_q,
                    )
                    / denominator;

            rubi_simp(&(first), x_) - second
        },
    ));
}

fn push_rules_rule_1457(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1457,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(b+q)/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c) \\[Star] Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;

            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(&b_plus_q / &a__)
                && !(negq!(&b_minus_q / &a__)
                    && rubi_simpler_sqrt_q(
                        &(-&b_minus_q / (Atom::num(2) * &a__)),
                        &(-&b_plus_q / (Atom::num(2) * &a__)),
                    ))
        },
        rhs: {
            let denominator = Atom::num(2) * &c__;
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(-&b_plus_q / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(
                        &((&b_plus_q + Atom::num(2) * &c__ * x_.pow(2))
                            / quartic.sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1458(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1458,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(b-q)/(2*c) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c) \\[Star] Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
         NegQ[(b-q)/a]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;

            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(&b_minus_q / &a__)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__;
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(-&b_minus_q / &denominator, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(
                        &((&b_minus_q + Atom::num(2) * &c__ * x_.pow(2))
                            / quartic.sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1459(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1459,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,2]},
          1/q \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_)) - rubi_star(Atom::num(1) / &q, rubi_rhs_int(
                        &((Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1460(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1460,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4] \\[Star]
            Int[x^2/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let b_plus_q = &b__ + &q;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_q).sqrt();
            let second_sqrt = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_q).sqrt();
            let transformed_integrand = x_.pow(2) / (&first_sqrt * &second_sqrt);
            rubi_star(&first_sqrt * &second_sqrt / quartic.sqrt(), rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1461(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1461,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/
            ((1+2*c*x^2/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^2/(b-Rt[b^2-4*a*c,2]))^FracPart[p]) \\[Star]
            Int[(d*x)^m*(1+2*c*x^2/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^2/(b-Sqrt[b^2-4*a*c]))^p,x] /;
        FreeQ[{a,b,c,d,m,p},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, p_], x_) },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let rt_discriminant = rubi_rt(&discriminant, 2);
            let sqrt_discriminant = discriminant.sqrt();
            let b_plus_rt = &b__ + &rt_discriminant;
            let b_minus_rt = &b__ - &rt_discriminant;
            let b_plus_sqrt = &b__ + &sqrt_discriminant;
            let b_minus_sqrt = &b__ - &sqrt_discriminant;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let frac_p = rubi_frac_part(&p_);
            let first = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_rt;
            let second = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_rt;
            let denominator = first.pow(&frac_p) * second.pow(&frac_p);
            let recursive_first =
                Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_sqrt;
            let recursive_second =
                Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_sqrt;
            let recursive_integrand = (&d__ * x_).pow(&m_)
                * recursive_first.pow(&p_)
                * recursive_second.pow(&p_);
            rubi_star(a__.pow(rubi_int_part(&p_)) * quartic.pow(&frac_p) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1462(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, u_, v_);
    let rule = rubi_rule!(
        order: 1462,
        source: "Int[u_^m_.*(a_.+b_.*v_^2+c_.*v_^4)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a+b*x^2+c*x^(2*2))^p,x],x,v] /;
        FreeQ[{a,b,c,m,p},x] && LinearPairQ[u,v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u_.pow(m_) * (a__ + b__ * v_.pow(2) + c__ * v_.pow(4)).pow(p_),
        with: [u_, a__, b__, c__, v_, m_, p_, x_],
        optional: [m_, a__, b__, c__, p_],
        x_dep: [],
        x_free: [a__, b__, c__, m_, p_],
        x_linear: [u_, v_],
        when: { freeq!([a__, b__, c__, m_, p_], x_) && rubi_linear_pair_q(&u_, &v_, x_) },
        rhs: {
            let coefficient = polynomial_coefficient(&v_, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(2)
                    + &c__ * sub_atom.pow(Atom::num(2) * Atom::num(2)))
                .pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                &v_,
            );
            rubi_star(u_.pow(&m_) / (&coefficient * v_.pow(&m_)), substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u_)
            .with_repeated_proper_x_dependent_subexpression(),
    );
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    x_.pow(2) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}
