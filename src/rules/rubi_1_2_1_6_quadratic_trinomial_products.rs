use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1329(rules);
    push_rules_rule_1330(rules);
    push_rules_rule_1331(rules);
    push_rules_rule_1332(rules);
    push_rules_rule_1333(rules);
    push_rules_rule_1334(rules);
    push_rules_rule_1335(rules);
    push_rules_rule_1336(rules);
    push_rules_rule_1337(rules);
    push_rules_rule_1338(rules);
    push_rules_rule_1339(rules);
    push_rules_rule_1340(rules);
    push_rules_rule_1341(rules);
    push_rules_rule_1342(rules);
    push_rules_rule_1343(rules);
    push_rules_rule_1344(rules);
    push_rules_rule_1345(rules);
    push_rules_rule_1346(rules);
    push_rules_rule_1347(rules);
    push_rules_rule_1348(rules);
    push_rules_rule_1349(rules);
    push_rules_rule_1350(rules);
    push_rules_rule_1351(rules);
    push_rules_rule_1352(rules);
    push_rules_rule_1353(rules);
    push_rules_rule_1354(rules);
    push_rules_rule_1355(rules);
    push_rules_rule_1356(rules);
    push_rules_rule_1357(rules);
    push_rules_rule_1358(rules);
    push_rules_rule_1359(rules);
    push_rules_rule_1360(rules);
    push_rules_rule_1361(rules);
    push_rules_rule_1362(rules);
    push_rules_rule_1363(rules);
    push_rules_rule_1364(rules);
    push_rules_rule_1365(rules);
    push_rules_rule_1366(rules);
    push_rules_rule_1367(rules);
    push_rules_rule_1368(rules);
    push_rules_rule_1369(rules);
    push_rules_rule_1370(rules);
    push_rules_rule_1371(rules);
    push_rules_rule_1372(rules);
    push_rules_rule_1373(rules);
    push_rules_rule_1374(rules);
    push_rules_rule_1375(rules);
    push_rules_rule_1376(rules);
    push_rules_rule_1377(rules);
    push_rules_rule_1378(rules);
}

fn push_rules_rule_1329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1329,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (c/f)^p \\[Star] Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) &&
          (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_],
        when: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_], x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && (integerq!(p_) || gtq!(&c__ / &f__, 0))
                && (!integerq!(q_)
                    || rubi_leaf_count(&second) <= rubi_leaf_count(&first))
        },
        rhs: {
            let recursive_integrand =
                (&g__ + &h__ * x_).pow(&m_) * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&p_ + &q_);
            rubi_star((&c__ / &f__).pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1330,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p]) \\[Star] Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_], x_)
                && eqq!(&c__ * &d__ - &a__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && !integerq!(p_)
                && !integerq!(q_)
                && !gtq!(&c__ / &f__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let denominator = d__.pow(rubi_int_part(&p_)) * second.pow(rubi_frac_part(&p_));
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_) * second.pow(&p_ + &q_);
            rubi_star(a__.pow(rubi_int_part(&p_)) * first.pow(rubi_frac_part(&p_)) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1331,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
          1/c^p \\[Star] Int[(g+h*x)^m*(b/2+c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,q},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_)
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1332,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] :=
          1/c^p \\[Star] Int[(g+h*x)^m*(b/2+c*x)^(2*p)*(d+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,f,g,h,m,q},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, d__, f__, g__, h__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, f__, g__, h__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__, m_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_)
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_)
                * (&d__ + &f__ * x_.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1333,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let frac_p = rubi_frac_part(&p_);
            let denominator = (Atom::num(4) * &c__).pow(rubi_int_part(&p_)) * linear.pow(Atom::num(2) * &frac_p);
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_) * linear.pow(Atom::num(2) * &p_) * second.pow(&q_);
            rubi_star(first.pow(frac_p) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1334,
        source: "Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
        FreeQ[{a,b,c,d,f,g,h,m,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, m_, p_, q_, x_],
        optional: [b__, c__, f__, g__, h__, m_],
        x_free: [a__, b__, c__, d__, f__, g__, h__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__, m_, p_, q_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let second = &d__ + &f__ * x_.pow(2);
            let frac_p = rubi_frac_part(&p_);
            let denominator = (Atom::num(4) * &c__).pow(rubi_int_part(&p_)) * linear.pow(Atom::num(2) * &frac_p);
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_) * linear.pow(Atom::num(2) * &p_) * second.pow(&q_);
            rubi_star(first.pow(frac_p) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1335,
        source: "Int[(g_+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^m_.,x_Symbol] :=
          Int[(d*g/a+f*h*x/c)^m*(a+b*x+c*x^2)^(m+p),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && EqQ[c^2*d*g^2-a*c*e*g*h+a^2*f*h^2,0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
            * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(m_),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, x_],
        optional: [b__, c__, d__, e__, f__, h__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && eqq!(&c__ * g__.pow(2) - &b__ * &g__ * &h__ + &a__ * h__.pow(2), 0)
                && eqq!(c__.pow(2) * &d__ * g__.pow(2) - &a__ * &c__ * &e__ * &g__ * &h__ + a__.pow(2) * &f__ * h__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let recursive_integrand = (&d__ * &g__ / &a__ + &f__ * &h__ * x_ / &c__).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&m_ + &p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, h__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1336,
        source: "Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^m_.,x_Symbol] :=
          Int[(d*g/a+f*h*x/c)^m*(a+c*x^2)^(m+p),x] /;
        FreeQ[{a,c,d,e,f,g,h,p},x] && EqQ[c*g^2+a*h^2,0] && EqQ[c^2*d*g^2-a*c*e*g*h+a^2*f*h^2,0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (a__ + c__ * x_.pow(2)).pow(p_)
            * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(m_),
        with: [a__, c__, d__, e__, f__, g__, h__, m_, p_, x_],
        optional: [c__, d__, e__, f__, h__, m_],
        x_free: [a__, c__, d__, e__, f__, g__, h__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__, p_], x_)
                && eqq!(&c__ * g__.pow(2) + &a__ * h__.pow(2), 0)
                && eqq!(c__.pow(2) * &d__ * g__.pow(2) - &a__ * &c__ * &e__ * &g__ * &h__ + a__.pow(2) * &f__ * h__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let recursive_integrand = (&d__ * &g__ / &a__ + &f__ * &h__ * x_ / &c__).pow(&m_)
                * (&a__ + &c__ * x_.pow(2)).pow(&m_ + &p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, h__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1337,
        source: "Int[(g_+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^m_.,x_Symbol] :=
          Int[(d*g/a+f*h*x/c)^m*(a+b*x+c*x^2)^(m+p),x] /;
        FreeQ[{a,b,c,d,f,g,h,p},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && EqQ[c^2*d*g^2+a^2*f*h^2,0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
            * (d__ + f__ * x_.pow(2)).pow(m_),
        with: [a__, b__, c__, d__, f__, g__, h__, m_, p_, x_],
        optional: [b__, c__, d__, f__, h__, m_],
        x_free: [a__, b__, c__, d__, f__, g__, h__, p_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__, p_], x_)
                && eqq!(&c__ * g__.pow(2) - &b__ * &g__ * &h__ + &a__ * h__.pow(2), 0)
                && eqq!(c__.pow(2) * &d__ * g__.pow(2) + a__.pow(2) * &f__ * h__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let recursive_integrand = (&d__ * &g__ / &a__ + &f__ * &h__ * x_ / &c__).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&m_ + &p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, f__, g__, h__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1338,
        source: "Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^m_.,x_Symbol] :=
          Int[(d*g/a+f*h*x/c)^m*(a+c*x^2)^(m+p),x] /;
        FreeQ[{a,c,d,f,g,h,p},x] && EqQ[c*g^2+a*h^2,0] && EqQ[c^2*d*g^2+a^2*f*h^2,0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (a__ + c__ * x_.pow(2)).pow(p_)
            * (d__ + f__ * x_.pow(2)).pow(m_),
        with: [a__, c__, d__, f__, g__, h__, m_, p_, x_],
        optional: [c__, d__, f__, h__, m_],
        x_free: [a__, c__, d__, f__, g__, h__, p_],
        when: {
            freeq!([a__, c__, d__, f__, g__, h__, p_], x_)
                && eqq!(&c__ * g__.pow(2) + &a__ * h__.pow(2), 0)
                && eqq!(c__.pow(2) * &d__ * g__.pow(2) + a__.pow(2) * &f__ * h__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let recursive_integrand = (&d__ * &g__ / &a__ + &f__ * &h__ * x_ / &c__).pow(&m_)
                * (&a__ + &c__ * x_.pow(2)).pow(&m_ + &p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1339,
        source: "Int[x_^p_*(a_.+b_.*x_+c_.*x_^2)^p_*(e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          Int[(a/e+c/f*x)^p*(e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,b,c,e,f,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*e^2-b*e*f+a*f^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(p_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (e__ * x_ + f__ * x_.pow(2)).pow(q_),
        with: [a__, b__, c__, e__, f__, p_, q_, x_],
        optional: [a__, b__, c__, e__, f__],
        x_free: [a__, b__, c__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, e__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * e__.pow(2) - &b__ * &e__ * &f__ + &a__ * f__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&a__ / &e__ + &c__ * x_ / &f__).pow(&p_) * (&e__ * x_ + &f__ * x_.pow(2)).pow(&p_ + &q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1340,
        source: "Int[x_^p_*(a_+c_.*x_^2)^p_*(e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
          Int[(a/e+c/f*x)^p*(e*x+f*x^2)^(p+q),x] /;
        FreeQ[{a,c,e,f,q},x] && EqQ[c*e^2+a*f^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(p_) * (a__ + c__ * x_.pow(2)).pow(p_) * (e__ * x_ + f__ * x_.pow(2)).pow(q_),
        with: [a__, c__, e__, f__, p_, q_, x_],
        optional: [c__, e__, f__],
        x_free: [a__, c__, e__, f__, q_],
        when: {
            freeq!([a__, c__, e__, f__, q_], x_)
                && eqq!(&c__ * e__.pow(2) + &a__ * f__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&a__ / &e__ + &c__ * x_ / &f__).pow(&p_) * (&e__ * x_ + &f__ * x_.pow(2)).pow(&p_ + &q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1341,
        source: "Int[(g_+h_.*x_)/((a_+c_.*x_^2)^(1/3)*(d_+f_.*x_^2)),x_Symbol] :=
          Sqrt[3]*h*ArcTan[1/Sqrt[3]-2^(2/3)*(1-3*h*x/g)^(2/3)/(Sqrt[3]*(1+3*h*x/g)^(1/3))]/(2^(2/3)*a^(1/3)*f) +
          h*Log[d+f*x^2]/(2^(5/3)*a^(1/3)*f) -
          3*h*Log[(1-3*h*x/g)^(2/3)+2^(1/3)*(1+3*h*x/g)^(1/3)]/(2^(5/3)*a^(1/3)*f) /;
        FreeQ[{a,c,d,f,g,h},x] && EqQ[c*d+3*a*f,0] && EqQ[c*g^2+9*a*h^2,0] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, f__, g__, h__, x_],
        optional: [c__, f__, h__],
        x_free: [a__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, f__, g__, h__], x_)
                && eqq!(&c__ * &d__ + Atom::num(3) * &a__ * &f__, 0)
                && eqq!(&c__ * g__.pow(2) + Atom::num(9) * &a__ * h__.pow(2), 0)
                && gtq!(a__, 0)
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let five_thirds = Atom::num(5) / Atom::num(3);
            let one_minus = Atom::num(1) - Atom::num(3) * &h__ * x_ / &g__;
            let one_plus = Atom::num(1) + Atom::num(3) * &h__ * x_ / &g__;
            let atan_argument = Atom::num(1) / &sqrt_three
                - Atom::num(2).pow((2, 3)) * one_minus.pow((2, 3))
                    / (&sqrt_three * one_plus.pow((1, 3)));
            let denominator = Atom::num(2).pow((2, 3)) * a__.pow((1, 3)) * &f__;
            let log_denominator = Atom::num(2).pow(five_thirds) * a__.pow((1, 3)) * &f__;

            rubi_simp(&(&sqrt_three * &h__ * atan_argument.atan() / denominator), x_)
                    + rubi_simp(&(&h__ * (&d__ + &f__ * x_.pow(2)).log() / &log_denominator), x_)
                    - rubi_simp(&(Atom::num(3)
                        * &h__
                        * (one_minus.pow((2, 3)) + Atom::num(2).pow(Atom::num(1) / Atom::num(3)) * one_plus.pow(Atom::num(1) / Atom::num(3)))
                            .log()
                        / log_denominator), x_)
        },
    ));
}

fn push_rules_rule_1342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1342,
        source: "Int[(g_+h_.*x_)/((a_+c_.*x_^2)^(1/3)*(d_+f_.*x_^2)),x_Symbol] :=
          (1+c*x^2/a)^(1/3)/(a+c*x^2)^(1/3) \\[Star] Int[(g+h*x)/((1+c*x^2/a)^(1/3)*(d+f*x^2)),x] /;
        FreeQ[{a,c,d,f,g,h},x] && EqQ[c*d+3*a*f,0] && EqQ[c*g^2+9*a*h^2,0] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, f__, g__, h__, x_],
        optional: [c__, f__, h__],
        x_free: [a__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, f__, g__, h__], x_)
                && eqq!(&c__ * &d__ + Atom::num(3) * &a__ * &f__, 0)
                && eqq!(&c__ * g__.pow(2) + Atom::num(9) * &a__ * h__.pow(2), 0)
                && !gtq!(a__, 0)
        },
        rhs: {
            let normalized = Atom::num(1) + &c__ * x_.pow(2) / &a__;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let recursive_integrand = (&g__ + &h__ * x_) / (normalized.pow(Atom::num(1) / Atom::num(3)) * (&d__ + &f__ * x_.pow(2)));
            rubi_star(normalized.pow(Atom::num(1) / Atom::num(3))
                    / quadratic.pow(Atom::num(1) / Atom::num(3)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1343,
        source: "Int[(g_+h_.*x_)*(a_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
          g \\[Star] Int[(a+c*x^2)^p*(d+f*x^2)^q,x] + h \\[Star] Int[x*(a+c*x^2)^p*(d+f*x^2)^q,x] /;
        FreeQ[{a,c,d,f,g,h,p,q},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ + h__ * x_) * (a__ + c__ * x_.pow(2)).pow(p_) * (d__ + f__ * x_.pow(2)).pow(q_),
        with: [a__, c__, d__, f__, g__, h__, p_, q_, x_],
        optional: [c__, f__, h__],
        x_free: [a__, c__, d__, f__, g__, h__, p_, q_],
        when: { freeq!([a__, c__, d__, f__, g__, h__, p_, q_], x_) },
        rhs: {
            let base = (&a__ + &c__ * x_.pow(2)).pow(&p_) * (&d__ + &f__ * x_.pow(2)).pow(&q_);
            rubi_star(g__, rubi_rhs_int(&base, x_))
                    + rubi_star(h__, rubi_rhs_int(&(x_ * base), x_))
        },
    ));
}

fn push_rules_rule_1344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1344,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && IGtQ[p,0] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && igtq!(p_, 0)
                && integerq!(q_)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_)
                * (&g__ + &h__ * x_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1345,
        source: "Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          Int[ExpandIntegrand[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x],x] /;
        FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && IntegersQ[p,q] && (GtQ[p,0] || GtQ[q,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [c__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && integersq!([p_, q_])
                && (gtq!(p_, 0) || gtq!(q_, 0))
        },
        rhs: {
            let integrand = (&a__ + &c__ * x_.pow(2)).pow(&p_)
                * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_)
                * (&g__ + &h__ * x_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1346,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (g*b-2*a*h-(b*h-2*g*c)*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((b^2-4*a*c)*(p+1)) -
          1/((b^2-4*a*c)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[e*q*(g*b-2*a*h)-d*(b*h-2*g*c)*(2*p+3)+
                (2*f*q*(g*b-2*a*h)-e*(b*h-2*g*c)*(2*p+q+3))*x-
                f*(b*h-2*g*c)*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Nondegenerate biquadratic recurrence 1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let u = &g__ * &b__ - Atom::num(2) * &a__ * &h__;
            let w = &b__ * &h__ - Atom::num(2) * &g__ * &c__;
            let direct = (&u - &w * x_) * first.pow(&p_ + Atom::num(1)) * second.pow(&q_) / &denominator;
            let polynomial = simp!(
                &e__ * &q_ * &u - &d__ * &w * (Atom::num(2) * &p_ + Atom::num(3))
                    + (Atom::num(2) * &f__ * &q_ * &u - &e__ * &w * (Atom::num(2) * &p_ + &q_ + Atom::num(3))) * x_
                    - &f__ * &w * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ - Atom::num(1)) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1347,
        source: "Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (a*h-g*c*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(2*a*c*(p+1)) +
          2/(4*a*c*(p+1)) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
              Simp[g*c*d*(2*p+3)-a*(h*e*q)+(g*c*e*(2*p+q+3)-a*(2*h*f*q))*x+g*c*f*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Nondegenerate biquadratic recurrence 1",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [c__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let recursive_denominator = Atom::num(4) * &a__ * &c__ * (&p_ + Atom::num(1));
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let direct = (&a__ * &h__ - &g__ * &c__ * x_) * first.pow(&p_ + Atom::num(1)) * second.pow(&q_) / &direct_denominator;
            let polynomial = simp!(
                &g__ * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3))
                    - &a__ * (&h__ * &e__ * &q_)
                    + (&g__ * &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(3))
                        - &a__ * (Atom::num(2) * &h__ * &f__ * &q_))
                        * x_
                    + &g__ * &c__ * &f__ * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ - Atom::num(1)) * polynomial;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(2) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1348,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (g*b-2*a*h-(b*h-2*g*c)*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/((b^2-4*a*c)*(p+1)) -
          1/((b^2-4*a*c)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
              Simp[-d*(b*h-2*g*c)*(2*p+3)+(2*f*q*(g*b-2*a*h))*x-f*(b*h-2*g*c)*(2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Nondegenerate biquadratic recurrence 1",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let u = &g__ * &b__ - Atom::num(2) * &a__ * &h__;
            let w = &b__ * &h__ - Atom::num(2) * &g__ * &c__;
            let direct = (&u - &w * x_) * first.pow(&p_ + Atom::num(1)) * second.pow(&q_) / &denominator;
            let polynomial = simp!(
                -&d__ * &w * (Atom::num(2) * &p_ + Atom::num(3))
                    + (Atom::num(2) * &f__ * &q_ * &u) * x_
                    - &f__ * &w * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ - Atom::num(1)) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1349,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
            (g*c*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+
              c*(g*(2*c^2*d+b^2*f-c*(b*e+2*a*f))-h*(b*c*d-2*a*c*e+a*b*f))*x) +
          1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[(b*h-2*g*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)+
                (b^2*(g*f)-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(a*f*(p+1)-c*d*(p+2))-
                e*((g*c)*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
                (2*f*((g*c)*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
                  (b^2*g*f-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)-a*(-h*c*e)))*
                  (b*f*(p+1)-c*e*(2*p+q+4)))*x-
                c*f*(b^2*(g*f)-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)+a*h*c*e))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,b,c,d,e,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] &&
          NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, q_],
        when: {
            let delta = (&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
        },
        rhs: {
            let delta = (&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__);
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * &delta * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let tail = Atom::num(2) * c__.pow(2) * &d__ + b__.pow(2) * &f__ - &c__ * (&b__ * &e__ + Atom::num(2) * &a__ * &f__);
            let lead = &g__ * &c__ * (Atom::num(2) * &a__ * &c__ * &e__ - &b__ * (&c__ * &d__ + &a__ * &f__))
                + (&g__ * &b__ - &a__ * &h__) * &tail;
            let x_lead =
                &c__ * (&g__ * &tail - &h__ * (&b__ * &c__ * &d__ - Atom::num(2) * &a__ * &c__ * &e__ + &a__ * &b__ * &f__));
            let u = b__.pow(2) * &g__ * &f__
                - &b__ * (&h__ * &c__ * &d__ + &g__ * &c__ * &e__ + &a__ * &h__ * &f__)
                + Atom::num(2) * (&g__ * &c__ * (&c__ * &d__ - &a__ * &f__) - &a__ * (Atom::num(-1) * &h__ * &c__ * &e__));
            let direct = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ + Atom::num(1)) * (&lead + x_lead * x_) / &denominator;
            let polynomial = simp!(
                (&b__ * &h__ - Atom::num(2) * &g__ * &c__) * &delta * (&p_ + Atom::num(1))
                    + &u * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    - &e__ * &lead * (&p_ + &q_ + Atom::num(2))
                    - (Atom::num(2) * &f__ * &lead * (&p_ + &q_ + Atom::num(2))
                        - &u * (&b__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(4))))
                        * x_
                    - &c__ * &f__ * &u * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1350,
        source: "Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
            (g*c*(2*a*c*e)+(-a*h)*(2*c^2*d-c*(2*a*f))+
              c*(g*(2*c^2*d-c*(2*a*f))-h*(-2*a*c*e))*x) +
          1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1)) \\[Star]
            Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
              Simp[(-2*g*c)*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)+
                (2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(a*f*(p+1)-c*d*(p+2))-
                e*((g*c)*(2*a*c*e)+(-a*h)*(2*c^2*d-c*(+2*a*f)))*(p+q+2)-
                (2*f*((g*c)*(2*a*c*e)+(-a*h)*(2*c^2*d+-c*(+2*a*f)))*(p+q+2)-(2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(-c*e*(2*p+q+4)))*x-
                c*f*(2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,c,d,e,f,g,h,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [c__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__, q_],
        when: {
            let delta = &a__ * &c__ * e__.pow(2) + (&c__ * &d__ - &a__ * &f__).pow(2);
            freeq!([a__, c__, d__, e__, f__, g__, h__, q_], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
        },
        rhs: {
            let delta = &a__ * &c__ * e__.pow(2) + (&c__ * &d__ - &a__ * &f__).pow(2);
            let denominator = Atom::num(-4) * &a__ * &c__ * &delta * (&p_ + Atom::num(1));
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let tail = Atom::num(2) * c__.pow(2) * &d__ - &c__ * (Atom::num(2) * &a__ * &f__);
            let lead = &g__ * &c__ * (Atom::num(2) * &a__ * &c__ * &e__) + (Atom::num(-1) * &a__ * &h__) * &tail;
            let x_lead = &c__ * (&g__ * &tail - &h__ * (Atom::num(-2) * &a__ * &c__ * &e__));
            let u = Atom::num(2) * (&g__ * &c__ * (&c__ * &d__ - &a__ * &f__) - &a__ * (Atom::num(-1) * &h__ * &c__ * &e__));
            let direct = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ + Atom::num(1)) * (&lead + x_lead * x_) / &denominator;
            let polynomial = simp!(
                (Atom::num(-2) * &g__ * &c__) * ((&c__ * &d__ - &a__ * &f__).pow(2) - (Atom::num(-1) * &a__ * &e__) * (&c__ * &e__)) * (&p_ + Atom::num(1))
                    + &u * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    - &e__ * &lead * (&p_ + &q_ + Atom::num(2))
                    - (Atom::num(2) * &f__ * &lead * (&p_ + &q_ + Atom::num(2))
                        - &u * (Atom::num(-1) * &c__ * &e__ * (Atom::num(2) * &p_ + &q_ + Atom::num(4))))
                        * x_
                    - &c__ * &f__ * &u * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1351,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          (a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
            ((g*c)*(-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(2*a*f))+
              c*(g*(2*c^2*d+b^2*f-c*(2*a*f))-h*(b*c*d+a*b*f))*x) +
          1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1)) \\[Star]
            Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
              Simp[(b*h-2*g*c)*((c*d-a*f)^2-(b*d)*(-b*f))*(p+1)+
                (b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*(a*f*(p+1)-c*d*(p+2))-
                (2*f*((g*c)*(-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(2*a*f)))*(p+q+2)-
                  (b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*
                  (b*f*(p+1)))*x-
                c*f*(b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*(2*p+2*q+5)*x^2,x],x]/;
        FreeQ[{a,b,c,d,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__, q_],
        when: {
            let delta = b__.pow(2) * &d__ * &f__ + (&c__ * &d__ - &a__ * &f__).pow(2);
            freeq!([a__, b__, c__, d__, f__, g__, h__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && neq!(delta, 0)
                && !(!integerq!(p_) && iltq!(q_, -1))
        },
        rhs: {
            let delta = b__.pow(2) * &d__ * &f__ + (&c__ * &d__ - &a__ * &f__).pow(2);
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__) * &delta * (&p_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let tail = Atom::num(2) * c__.pow(2) * &d__ + b__.pow(2) * &f__ - &c__ * (Atom::num(2) * &a__ * &f__);
            let lead = &g__ * &c__ * (Atom::num(-1) * &b__ * (&c__ * &d__ + &a__ * &f__)) + (&g__ * &b__ - &a__ * &h__) * &tail;
            let x_lead = &c__ * (&g__ * &tail - &h__ * (&b__ * &c__ * &d__ + &a__ * &b__ * &f__));
            let u = b__.pow(2) * &g__ * &f__ - &b__ * (&h__ * &c__ * &d__ + &a__ * &h__ * &f__) + Atom::num(2) * (&g__ * &c__ * (&c__ * &d__ - &a__ * &f__));
            let direct = first.pow(&p_ + Atom::num(1)) * second.pow(&q_ + Atom::num(1)) * (&lead + x_lead * x_) / &denominator;
            let polynomial = simp!(
                (&b__ * &h__ - Atom::num(2) * &g__ * &c__) * ((&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__) * (Atom::num(-1) * &b__ * &f__)) * (&p_ + Atom::num(1))
                    + &u * (&a__ * &f__ * (&p_ + Atom::num(1)) - &c__ * &d__ * (&p_ + Atom::num(2)))
                    - (Atom::num(2) * &f__ * &lead * (&p_ + &q_ + Atom::num(2)) - &u * (&b__ * &f__ * (&p_ + Atom::num(1)))) * x_
                    - &c__ * &f__ * &u * (Atom::num(2) * &p_ + Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ + Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1352,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          h*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q+1)/(2*f*(p+q+1)) -
          (1/(2*f*(p+q+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
              Simp[h*p*(b*d-a*e)+a*(h*e-2*g*f)*(p+q+1)+
                (2*h*p*(c*d-a*f)+b*(h*e-2*g*f)*(p+q+1))*x+
                (h*p*(c*e-b*f)+c*(h*e-2*g*f)*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0]",
        desc: "Nondegenerate biquadratic recurrence 2",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &f__ * (&p_ + &q_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let w = &h__ * &e__ - Atom::num(2) * &g__ * &f__;
            let direct = &h__ * first.pow(&p_) * second.pow(&q_ + Atom::num(1)) / &denominator;
            let polynomial = simp!(
                &h__ * &p_ * (&b__ * &d__ - &a__ * &e__) + &a__ * &w * (&p_ + &q_ + Atom::num(1))
                    + (Atom::num(2) * &h__ * &p_ * (&c__ * &d__ - &a__ * &f__) + &b__ * &w * (&p_ + &q_ + Atom::num(1))) * x_
                    + (&h__ * &p_ * (&c__ * &e__ - &b__ * &f__) + &c__ * &w * (&p_ + &q_ + Atom::num(1))) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1353,
        source: "Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          h*(a+c*x^2)^p*(d+e*x+f*x^2)^(q+1)/(2*f*(p+q+1)) +
          (1/(2*f*(p+q+1))) \\[Star]
            Int[(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
              Simp[a*h*e*p-a*(h*e-2*g*f)*(p+q+1)-2*h*p*(c*d-a*f)*x-(h*c*e*p+c*(h*e-2*g*f)*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g,h,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0]",
        desc: "Nondegenerate biquadratic recurrence 2",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [c__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__, q_], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &f__ * (&p_ + &q_ + Atom::num(1));
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let w = &h__ * &e__ - Atom::num(2) * &g__ * &f__;
            let direct = &h__ * first.pow(&p_) * second.pow(&q_ + Atom::num(1)) / &denominator;
            let polynomial = simp!(
                &a__ * &h__ * &e__ * &p_ - &a__ * &w * (&p_ + &q_ + Atom::num(1))
                    - Atom::num(2) * &h__ * &p_ * (&c__ * &d__ - &a__ * &f__) * x_
                    - (&h__ * &c__ * &e__ * &p_ + &c__ * &w * (&p_ + &q_ + Atom::num(1))) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1354,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          h*(a+b*x+c*x^2)^p*(d+f*x^2)^(q+1)/(2*f*(p+q+1)) -
          (1/(2*f*(p+q+1))) \\[Star]
            Int[(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^q*
              Simp[h*p*(b*d)+a*(-2*g*f)*(p+q+1)+
                (2*h*p*(c*d-a*f)+b*(-2*g*f)*(p+q+1))*x+
                (h*p*(-b*f)+c*(-2*g*f)*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[p+q+1,0]",
        desc: "Nondegenerate biquadratic recurrence 2",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, p_, q_, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__, q_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && neq!(&p_ + &q_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &f__ * (&p_ + &q_ + Atom::num(1));
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let w = Atom::num(-2) * &g__ * &f__;
            let direct = &h__ * first.pow(&p_) * second.pow(&q_ + Atom::num(1)) / &denominator;
            let polynomial = simp!(
                &h__ * &p_ * (&b__ * &d__) + &a__ * &w * (&p_ + &q_ + Atom::num(1))
                    + (Atom::num(2) * &h__ * &p_ * (&c__ * &d__ - &a__ * &f__) + &b__ * &w * (&p_ + &q_ + Atom::num(1))) * x_
                    + (&h__ * &p_ * (Atom::num(-1) * &b__ * &f__) + &c__ * &w * (&p_ + &q_ + Atom::num(1))) * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow(&p_ - Atom::num(1)) * second.pow(&q_) * polynomial;
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1355,
        source: "Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
          With[{q=Simplify[c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2]},
          1/q \\[Star] Int[Simp[g*c^2*d-g*b*c*e+a*h*c*e+g*b^2*f-a*b*h*f-a*g*c*f+c*(h*c*d-g*c*e+g*b*f-a*h*f)*x,x]/(a+b*x+c*x^2),x] +
          1/q \\[Star] Int[Simp[-h*c*d*e+g*c*e^2+b*h*d*f-g*c*d*f-g*b*e*f+a*g*f^2-f*(h*c*d-g*c*e+g*b*f-a*h*f)*x,x]/(d+e*x+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ + h__ * x_)
            / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            let q = simp!(
                c__.pow(2) * d__.pow(2) - &b__ * &c__ * &d__ * &e__ + &a__ * &c__ * e__.pow(2) + b__.pow(2) * &d__ * &f__
                    - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                    - &a__ * &b__ * &e__ * &f__
                    + a__.pow(2) * f__.pow(2),
                x_
            );
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(q, 0)
        },
        rhs: {
            let q = simp!(
                c__.pow(2) * d__.pow(2) - &b__ * &c__ * &d__ * &e__ + &a__ * &c__ * e__.pow(2) + b__.pow(2) * &d__ * &f__
                    - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                    - &a__ * &b__ * &e__ * &f__
                    + a__.pow(2) * f__.pow(2),
                x_
            );
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_numerator = simp!(
                &g__ * c__.pow(2) * &d__ - &g__ * &b__ * &c__ * &e__ + &a__ * &h__ * &c__ * &e__ + &g__ * b__.pow(2) * &f__
                    - &a__ * &b__ * &h__ * &f__
                    - &a__ * &g__ * &c__ * &f__
                    + &c__ * (&h__ * &c__ * &d__ - &g__ * &c__ * &e__ + &g__ * &b__ * &f__ - &a__ * &h__ * &f__) * x_,
                x_
            );
            let second_numerator = simp!(
                Atom::num(-1) * &h__ * &c__ * &d__ * &e__ + &g__ * &c__ * e__.pow(2) + &b__ * &h__ * &d__ * &f__
                    - &g__ * &c__ * &d__ * &f__
                    - &g__ * &b__ * &e__ * &f__
                    + &a__ * &g__ * f__.pow(2)
                    - &f__ * (&h__ * &c__ * &d__ - &g__ * &c__ * &e__ + &g__ * &b__ * &f__ - &a__ * &h__ * &f__) * x_,
                x_
            );
            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&(first_numerator / first), x_)) + rubi_star(Atom::num(1) / q, rubi_rhs_int(&(second_numerator / second), x_))
        },
    ));
}

fn push_rules_rule_1356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1356,
        source: "Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
          With[{q=Simplify[c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2]},
          1/q \\[Star] Int[Simp[g*c^2*d+g*b^2*f-a*b*h*f-a*g*c*f+c*(h*c*d+g*b*f-a*h*f)*x,x]/(a+b*x+c*x^2),x] +
          1/q \\[Star] Int[Simp[b*h*d*f-g*c*d*f+a*g*f^2-f*(h*c*d+g*b*f-a*h*f)*x,x]/(d+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (g__ + h__ * x_) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2))),
        with: [a__, b__, c__, d__, f__, g__, h__, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            let q = simp!(
                c__.pow(2) * d__.pow(2) + b__.pow(2) * &d__ * &f__ - Atom::num(2) * &a__ * &c__ * &d__ * &f__ + a__.pow(2) * f__.pow(2),
                x_
            );
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(q, 0)
        },
        rhs: {
            let q = simp!(
                c__.pow(2) * d__.pow(2) + b__.pow(2) * &d__ * &f__ - Atom::num(2) * &a__ * &c__ * &d__ * &f__ + a__.pow(2) * f__.pow(2),
                x_
            );
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let first_numerator = simp!(
                &g__ * c__.pow(2) * &d__ + &g__ * b__.pow(2) * &f__ - &a__ * &b__ * &h__ * &f__ - &a__ * &g__ * &c__ * &f__
                    + &c__ * (&h__ * &c__ * &d__ + &g__ * &b__ * &f__ - &a__ * &h__ * &f__) * x_,
                x_
            );
            let second_numerator = simp!(
                &b__ * &h__ * &d__ * &f__ - &g__ * &c__ * &d__ * &f__ + &a__ * &g__ * f__.pow(2)
                    - &f__ * (&h__ * &c__ * &d__ + &g__ * &b__ * &f__ - &a__ * &h__ * &f__) * x_,
                x_
            );
            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&(first_numerator / first), x_)) + rubi_star(Atom::num(1) / q, rubi_rhs_int(&(second_numerator / second), x_))
        },
    ));
}

fn push_rules_rule_1357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1357,
        source: "Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -2*g \\[Star] Subst[Int[1/(b*d-a*e-b*x^2),x],x,Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && EqQ[h*e-2*g*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, d__, e__, f__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&c__ * &e__ - &b__ * &f__, 0)
                && eqq!(&h__ * &e__ - Atom::num(2) * &g__ * &f__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                Atom::num(1) / (&b__ * &d__ - &a__ * &e__ - &b__ * sub_atom.pow(2));
            let substitution = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(-2) * &g__, rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1358,
        source: "Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -(h*e-2*g*f)/(2*f) \\[Star] Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] +
          h/(2*f) \\[Star] Int[(e+2*f*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && NeQ[h*e-2*g*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&c__ * &e__ - &b__ * &f__, 0)
                && neq!(&h__ * &e__ - Atom::num(2) * &g__ * &f__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &f__;
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            rubi_star(-(&h__ * &e__ - Atom::num(2) * &g__ * &f__) / &denominator, rubi_rhs_int(&(Atom::num(1) / (&first * second.sqrt())), x_)) + rubi_star(&h__ / denominator, rubi_rhs_int(
                        &((&e__ + Atom::num(2) * &f__ * x_)
                            / (first * second.sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 1359,
        source: "Int[x_/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -2*e \\[Star] Subst[Int[(1-d*x^2)/(c*e-b*f-e*(2*c*d-b*e+2*a*f)*x^2+d^2*(c*e-b*f)*x^4),x],x,
            (1+(e+Sqrt[e^2-4*d*f])*x/(2*d))/Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (Atom::num(1) - &d__ * sub_atom.pow(2))
                / (&c__ * &e__
                    - &b__ * &f__
                    - &e__
                        * (Atom::num(2) * &c__ * &d__ - &b__ * &e__
                            + Atom::num(2) * &a__ * &f__)
                        * sub_atom.pow(2)
                    + d__.pow(2) * (&c__ * &e__ - &b__ * &f__) * sub_atom.pow(4));
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let substitution = (Atom::num(1)
                + (&e__ + (e__.pow(2) - Atom::num(4) * &d__ * &f__).sqrt()) * x_ / (Atom::num(2) * &d__))
                / second.sqrt();

            rubi_star(Atom::num(-2) * &e__, rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1360,
        source: "Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
          g \\[Star] Subst[Int[1/(a+(c*d-a*f)*x^2),x],x,x/Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0] && EqQ[2*h*d-g*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, e__, f__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && eqq!(Atom::num(2) * &h__ * &d__ - &g__ * &e__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                Atom::num(1) / (&a__ + (&c__ * &d__ - &a__ * &f__) * sub_atom.pow(2));
            let substitution = x_ / (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();

            rubi_star(g__, rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1361,
        source: "Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -(2*h*d-g*e)/e \\[Star] Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] +
          h/e \\[Star] Int[(2*d+e*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0] && NeQ[2*h*d-g*e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, e__, f__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && neq!(Atom::num(2) * &h__ * &d__ - &g__ * &e__, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            rubi_star(-(&Atom::num(2) * &h__ * &d__ - &g__ * &e__) / &e__, rubi_rhs_int(&(Atom::num(1) / (&first * second.sqrt())), x_)) + rubi_star(&h__ / &e__, rubi_rhs_int(
                        &((Atom::num(2) * &d__ + &e__ * x_)
                            / (first * second.sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1362,
        source: "Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -2*g*(g*b-2*a*h) \\[Star]
            Subst[Int[1/Simp[g*(g*b-2*a*h)*(b^2-4*a*c)-(b*d-a*e)*x^2,x],x],x,Simp[g*b-2*a*h-(b*h-2*g*c)*x,x]/Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[b*d-a*e,0] &&
          EqQ[h^2*(b*d-a*e)-2*g*h*(c*d-a*f)+g^2*(c*e-b*f),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(&b__ * &d__ - &a__ * &e__, 0)
                && eqq!(
                    h__.pow(2) * (&b__ * &d__ - &a__ * &e__)
                        - Atom::num(2) * &g__ * &h__ * (&c__ * &d__ - &a__ * &f__)
                        + g__.pow(2) * (&c__ * &e__ - &b__ * &f__),
                    0
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / simp!(
                    &g__ * (&g__ * &b__ - Atom::num(2) * &a__ * &h__) * (b__.pow(2) - Atom::num(4) * &a__ * &c__)
                        - (&b__ * &d__ - &a__ * &e__) * sub_atom.pow(2),
                    sub
                );
            let substitution = simp!(
                &g__ * &b__ - Atom::num(2) * &a__ * &h__ - (&b__ * &h__ - Atom::num(2) * &g__ * &c__) * x_,
                x_
            ) / (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(-2)
                    * &g__
                    * (&g__ * &b__ - Atom::num(2) * &a__ * &h__), rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1363,
        source: "Int[(g_+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          -2*a*g*h \\[Star] Subst[Int[1/Simp[2*a^2*g*h*c+a*e*x^2,x],x],x,Simp[a*h-g*c*x,x]/Sqrt[d+e*x+f*x^2]] /;
        FreeQ[{a,c,d,e,f,g,h},x] && EqQ[a*h^2*e+2*g*h*(c*d-a*f)-g^2*c*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, x_],
        optional: [c__, d__, e__, f__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(
                    &a__ * h__.pow(2) * &e__ + Atom::num(2) * &g__ * &h__ * (&c__ * &d__ - &a__ * &f__) - g__.pow(2) * &c__ * &e__,
                    0
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / simp!(
                    Atom::num(2) * a__.pow(2) * &g__ * &h__ * &c__ + &a__ * &e__ * sub_atom.pow(2),
                    sub
                );
            let substitution =
                simp!(&a__ * &h__ - &g__ * &c__ * x_, x_) / (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(-2) * &a__ * &g__ * &h__, rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1364,
        source: "Int[(g_+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          -2*g*(g*b-2*a*h) \\[Star] Subst[Int[1/Simp[g*(g*b-2*a*h)*(b^2-4*a*c)-b*d*x^2,x],x],x,Simp[g*b-2*a*h-(b*h-2*g*c)*x,x]/Sqrt[d+f*x^2]] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && EqQ[b*h^2*d-2*g*h*(c*d-a*f)-g^2*b*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, x_],
        optional: [a__, b__, c__, f__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(
                    &b__ * h__.pow(2) * &d__ - Atom::num(2) * &g__ * &h__ * (&c__ * &d__ - &a__ * &f__) - g__.pow(2) * &b__ * &f__,
                    0
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / simp!(
                    &g__ * (&g__ * &b__ - Atom::num(2) * &a__ * &h__) * (b__.pow(2) - Atom::num(4) * &a__ * &c__)
                        - &b__ * &d__ * sub_atom.pow(2),
                    sub
                );
            let substitution = simp!(
                &g__ * &b__ - Atom::num(2) * &a__ * &h__ - (&b__ * &h__ - Atom::num(2) * &g__ * &c__) * x_,
                x_
            ) / (&d__ + &f__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(-2)
                    * &g__
                    * (&g__ * &b__ - Atom::num(2) * &a__ * &h__), rubi_subst(
                    &rubi_rhs_int(&transformed_integrand, sub),
                    sub,
                    substitution,
                ))
        },
    ));
}

fn push_rules_rule_1365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1365,
        source: "Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*c*g-h*(b-q))/q \\[Star] Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
          (2*c*g-h*(b+q))/q \\[Star] Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            rubi_star((Atom::num(2) * &c__ * &g__ - &h__ * (&b__ - &q)) / &q, rubi_rhs_int(
                        &(Atom::num(1)
                            / ((&b__ - &q + Atom::num(2) * &c__ * x_)
                                * second.sqrt())),
                        x_,
                    )) - rubi_star((Atom::num(2) * &c__ * &g__ - &h__ * (&b__ + &q)) / &q, rubi_rhs_int(
                        &(Atom::num(1)
                            / ((&b__ + &q + Atom::num(2) * &c__ * x_)
                                * second.sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1366,
        source: "Int[(g_.+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          (h/2+c*g/(2*q)) \\[Star] Int[1/((-q+c*x)*Sqrt[d+e*x+f*x^2]),x] +
          (h/2-c*g/(2*q)) \\[Star] Int[1/((q+c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && PosQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, x_],
        optional: [c__, d__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && posq!(-&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            rubi_star(&h__ / Atom::num(2) + &c__ * &g__ / (Atom::num(2) * &q), rubi_rhs_int(
                        &(Atom::num(1) / ((-&q + &c__ * x_) * second.sqrt())),
                        x_,
                    )) + rubi_star(&h__ / Atom::num(2) - &c__ * &g__ / (Atom::num(2) * &q), rubi_rhs_int(
                        &(Atom::num(1) / ((&q + &c__ * x_) * second.sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1367,
        source: "Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*c*g-h*(b-q))/q \\[Star] Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
          (2*c*g-h*(b+q))/q \\[Star] Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let second = &d__ + &f__ * x_.pow(2);
            rubi_star((Atom::num(2) * &c__ * &g__ - &h__ * (&b__ - &q)) / &q, rubi_rhs_int(
                        &(Atom::num(1)
                            / ((&b__ - &q + Atom::num(2) * &c__ * x_)
                                * second.sqrt())),
                        x_,
                    )) - rubi_star((Atom::num(2) * &c__ * &g__ - &h__ * (&b__ + &q)) / &q, rubi_rhs_int(
                        &(Atom::num(1)
                            / ((&b__ + &q + Atom::num(2) * &c__ * x_)
                                * second.sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_1368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1368,
        source: "Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),2]},
          1/(2*q) \\[Star] Int[Simp[h*(b*d-a*e)-g*(c*d-a*f-q)-(g*(c*e-b*f)-h*(c*d-a*f+q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] -
          1/(2*q) \\[Star] Int[Simp[h*(b*d-a*e)-g*(c*d-a*f+q)-(g*(c*e-b*f)-h*(c*d-a*f-q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[b*d-a*e,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && neq!(&b__ * &d__ - &a__ * &e__, 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(
                &((&c__ * &d__ - &a__ * &f__).pow(2) - (&b__ * &d__ - &a__ * &e__) * (&c__ * &e__ - &b__ * &f__)),
                2,
            );
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_numerator = simp!(
                &h__ * (&b__ * &d__ - &a__ * &e__) - &g__ * (&c__ * &d__ - &a__ * &f__ - &q)
                    - (&g__ * (&c__ * &e__ - &b__ * &f__) - &h__ * (&c__ * &d__ - &a__ * &f__ + &q)) * x_,
                x_
            );
            let second_numerator = simp!(
                &h__ * (&b__ * &d__ - &a__ * &e__) - &g__ * (&c__ * &d__ - &a__ * &f__ + &q)
                    - (&g__ * (&c__ * &e__ - &b__ * &f__) - &h__ * (&c__ * &d__ - &a__ * &f__ - &q)) * x_,
                x_
            );
            let first_recursive = rubi_rhs_int(
                &(first_numerator / (&first * second.sqrt())),
                x_,
            );
            let second_recursive = rubi_rhs_int(
                &(second_numerator / (first * second.sqrt())),
                x_,
            );
            let factor = Atom::num(1) / (Atom::num(2) * &q);

            rubi_star(&factor, first_recursive)
                    - rubi_star(factor, second_recursive)
        },
    ));
}

fn push_rules_rule_1369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1369,
        source: "Int[(g_.+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2+a*c*e^2,2]},
          1/(2*q) \\[Star] Int[Simp[-a*h*e-g*(c*d-a*f-q)+(h*(c*d-a*f+q)-g*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] -
          1/(2*q) \\[Star] Int[Simp[-a*h*e-g*(c*d-a*f+q)+(h*(c*d-a*f-q)-g*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && NegQ[-a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, x_],
        optional: [c__, d__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
                && negq!(-&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&((&c__ * &d__ - &a__ * &f__).pow(2) + &a__ * &c__ * e__.pow(2)), 2);
            let first = &a__ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let first_numerator = simp!(
                -&a__ * &h__ * &e__ - &g__ * (&c__ * &d__ - &a__ * &f__ - &q)
                    + (&h__ * (&c__ * &d__ - &a__ * &f__ + &q) - &g__ * &c__ * &e__) * x_,
                x_
            );
            let second_numerator = simp!(
                -&a__ * &h__ * &e__ - &g__ * (&c__ * &d__ - &a__ * &f__ + &q)
                    + (&h__ * (&c__ * &d__ - &a__ * &f__ - &q) - &g__ * &c__ * &e__) * x_,
                x_
            );
            let first_recursive = rubi_rhs_int(
                &(first_numerator / (&first * second.sqrt())),
                x_,
            );
            let second_recursive = rubi_rhs_int(
                &(second_numerator / (first * second.sqrt())),
                x_,
            );
            let factor = Atom::num(1) / (Atom::num(2) * &q);

            rubi_star(&factor, first_recursive)
                    - rubi_star(factor, second_recursive)
        },
    ));
}

fn push_rules_rule_1370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1370,
        source: "Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          With[{q=Rt[(c*d-a*f)^2+b^2*d*f,2]},
          1/(2*q) \\[Star] Int[Simp[h*b*d-g*(c*d-a*f-q)+(h*(c*d-a*f+q)+g*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] -
          1/(2*q) \\[Star] Int[Simp[h*b*d-g*(c*d-a*f+q)+(h*(c*d-a*f-q)+g*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, f__, g__, h__, x_],
        optional: [a__, b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&((&c__ * &d__ - &a__ * &f__).pow(2) + b__.pow(2) * &d__ * &f__), 2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let first_numerator = simp!(
                &h__ * &b__ * &d__ - &g__ * (&c__ * &d__ - &a__ * &f__ - &q)
                    + (&h__ * (&c__ * &d__ - &a__ * &f__ + &q) + &g__ * &b__ * &f__) * x_,
                x_
            );
            let second_numerator = simp!(
                &h__ * &b__ * &d__ - &g__ * (&c__ * &d__ - &a__ * &f__ + &q)
                    + (&h__ * (&c__ * &d__ - &a__ * &f__ - &q) + &g__ * &b__ * &f__) * x_,
                x_
            );
            let first_recursive = rubi_rhs_int(
                &(first_numerator / (&first * second.sqrt())),
                x_,
            );
            let second_recursive = rubi_rhs_int(
                &(second_numerator / (first * second.sqrt())),
                x_,
            );
            let factor = Atom::num(1) / (Atom::num(2) * &q);

            rubi_star(&factor, first_recursive)
                    - rubi_star(factor, second_recursive)
        },
    ));
}

fn push_rules_rule_1371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1371,
        source: "Int[(g_.+h_.*x_)/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{s=Rt[b^2-4*a*c,2],t=Rt[e^2-4*d*f,2]},
          Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[e+t+2*f*x]*Sqrt[2*d+(e+t)*x]/(Sqrt[a+b*x+c*x^2]*Sqrt[d+e*x+f*x^2]) \\[Star]
            Int[(g+h*x)/(Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[e+t+2*f*x]*Sqrt[2*d+(e+t)*x]),x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ + h__ * x_)
            / ((a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [b__, c__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(e__.pow(2) - Atom::num(4) * &d__ * &f__, 0)
        },
        rhs: {
            let s = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let t = rubi_rt(&(e__.pow(2) - Atom::num(4) * &d__ * &f__), 2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let u1 = &b__ + &s + Atom::num(2) * &c__ * x_;
            let u2 = Atom::num(2) * &a__ + (&b__ + &s) * x_;
            let v1 = &e__ + &t + Atom::num(2) * &f__ * x_;
            let v2 = Atom::num(2) * &d__ + (&e__ + &t) * x_;
            let transformed_integrand =
                (&g__ + &h__ * x_) / (u1.sqrt() * u2.sqrt() * v1.sqrt() * v2.sqrt());
            let factor = u1.sqrt() * u2.sqrt() * v1.sqrt() * v2.sqrt()
                / (first.sqrt() * second.sqrt());
            rubi_star(factor, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1372,
        source: "Int[(g_.+h_.*x_)/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
          With[{s=Rt[b^2-4*a*c,2],t=Rt[-4*d*f,2]},
          Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[t+2*f*x]*Sqrt[2*d+t*x]/(Sqrt[a+b*x+c*x^2]*Sqrt[d+f*x^2]) \\[Star]
            Int[(g+h*x)/(Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[t+2*f*x]*Sqrt[2*d+t*x]),x]] /;
        FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ + h__ * x_) / ((a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() * (d__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, f__, g__, h__, x_],
        optional: [b__, c__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, h__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let s = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let t = rubi_rt(&(-Atom::num(4) * &d__ * &f__), 2);
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &f__ * x_.pow(2);
            let u1 = &b__ + &s + Atom::num(2) * &c__ * x_;
            let u2 = Atom::num(2) * &a__ + (&b__ + &s) * x_;
            let v1 = &t + Atom::num(2) * &f__ * x_;
            let v2 = Atom::num(2) * &d__ + &t * x_;
            let transformed_integrand =
                (&g__ + &h__ * x_) / (u1.sqrt() * u2.sqrt() * v1.sqrt() * v2.sqrt());
            let factor = u1.sqrt() * u2.sqrt() * v1.sqrt() * v2.sqrt()
                / (first.sqrt() * second.sqrt());
            rubi_star(factor, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_1373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1373,
        source: "Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)^(1/3)*(d_.+e_.*x_+f_.*x_^2)),x_Symbol] :=
          With[{q=(-9*c*h^2/(2*c*g-b*h)^2)^(1/3)},
          Sqrt[3]*h*q*ArcTan[1/Sqrt[3]-2^(2/3)*(1-(3*h*(b+2*c*x))/(2*c*g-b*h))^(2/3)/(Sqrt[3]*(1+(3*h*(b+2*c*x))/(2*c*g-b*h))^(1/3))]/f +
          h*q*Log[d+e*x+f*x^2]/(2*f) -
          3*h*q*Log[(1-3*h*(b+2*c*x)/(2*c*g-b*h))^(2/3)+2^(1/3)*(1+3*h*(b+2*c*x)/(2*c*g-b*h))^(1/3)]/(2*f)] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[c*e-b*f,0] && EqQ[c^2*d-f*(b^2-3*a*c),0] && EqQ[c^2*g^2-b*c*g*h-2*b^2*h^2+9*a*c*h^2,0] &&
          GtQ[-9*c*h^2/(2*c*g-b*h)^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            let denominator = Atom::num(2) * &c__ * &g__ - &b__ * &h__;
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&c__ * &e__ - &b__ * &f__, 0)
                && eqq!(c__.pow(2) * &d__ - &f__ * (b__.pow(2) - Atom::num(3) * &a__ * &c__), 0)
                && eqq!(
                    c__.pow(2) * g__.pow(2) - &b__ * &c__ * &g__ * &h__ - Atom::num(2) * b__.pow(2) * h__.pow(2)
                        + Atom::num(9) * &a__ * &c__ * h__.pow(2),
                    0
                )
                && gtq!(-Atom::num(9) * &c__ * h__.pow(2) / denominator.pow(2), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * &g__ - &b__ * &h__;
            let sqrt_three = Atom::num(3).sqrt();
            let q = (-Atom::num(9) * &c__ * h__.pow(2) / denominator.pow(2)).pow((1, 3));
            let shifted = Atom::num(3) * &h__ * (&b__ + Atom::num(2) * &c__ * x_) / &denominator;
            let one_minus = Atom::num(1) - &shifted;
            let one_plus = Atom::num(1) + &shifted;
            let atan_argument = Atom::num(1) / &sqrt_three
                - Atom::num(2).pow((2, 3)) * one_minus.pow((2, 3))
                    / (&sqrt_three * one_plus.pow((1, 3)));
            let log_argument =
                one_minus.pow((2, 3)) + Atom::num(2).pow((1, 3)) * one_plus.pow((1, 3));
            let log_denominator = Atom::num(2) * &f__;

            rubi_simp(&(&sqrt_three * &h__ * &q * atan_argument.atan() / &f__), x_)
                    + rubi_simp(&(&h__ * &q * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).log() / &log_denominator), x_)
                    - rubi_simp(&(Atom::num(3) * &h__ * q * log_argument.log() / log_denominator), x_)
        },
    ));
}

fn push_rules_rule_1374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 1374,
        source: "Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)^(1/3)*(d_.+e_.*x_+f_.*x_^2)),x_Symbol] :=
          With[{q=-c/(b^2-4*a*c)},
          (q*(a+b*x+c*x^2))^(1/3)/(a+b*x+c*x^2)^(1/3) \\[Star] Int[(g+h*x)/((q*a+b*q*x+c*q*x^2)^(1/3)*(d+e*x+f*x^2)),x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[c*e-b*f,0] && EqQ[c^2*d-f*(b^2-3*a*c),0] && EqQ[c^2*g^2-b*c*g*h-2*b^2*h^2+9*a*c*h^2,0] && Not[GtQ[4*a-b^2/c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&c__ * &e__ - &b__ * &f__, 0)
                && eqq!(c__.pow(2) * &d__ - &f__ * (b__.pow(2) - Atom::num(3) * &a__ * &c__), 0)
                && eqq!(
                    c__.pow(2) * g__.pow(2) - &b__ * &c__ * &g__ * &h__ - Atom::num(2) * b__.pow(2) * h__.pow(2)
                        + Atom::num(9) * &a__ * &c__ * h__.pow(2),
                    0
                )
                && !gtq!(Atom::num(4) * &a__ - b__.pow(2) / &c__, 0)
        },
        rhs: {
            let q_denominator = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = -&c__ / q_denominator;
            let first = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let second = &d__ + &e__ * x_ + &f__ * x_.pow(2);
            let transformed_first = &q * &a__ + &b__ * &q * x_ + &c__ * &q * x_.pow(2);
            let recursive_integrand =
                (&g__ + &h__ * x_) / (transformed_first.pow(Atom::num(1) / Atom::num(3)) * second);
            let factor = (&q * &first).pow(Atom::num(1) / Atom::num(3))
                / first.pow(Atom::num(1) / Atom::num(3));
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1375,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          Unintegrable[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, q_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_)
                    * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_)
                    * (&g__ + &h__ * x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, h__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1376,
        source: "Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
          Unintegrable[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x] /;
        FreeQ[{a,c,d,e,f,g,h,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, h__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, c__, d__, e__, f__, g__, h__, p_, q_],
        when: { freeq!([a__, c__, d__, e__, f__, g__, h__, p_, q_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &c__ * x_.pow(2)).pow(&p_)
                    * (&d__ + &e__ * x_ + &f__ * x_.pow(2)).pow(&q_)
                    * (&g__ + &h__ * x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_, u__);
    rules.push(rubi_rule!(
        order: 1377,
        source: "Int[(g_.+h_.*u_)^m_.*(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(g+h*x)^m*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * u__).pow(m_)
            * (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, u__, m_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&g__ + &h__ * &sub_atom).pow(&m_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_);
            rubi_star(Atom::num(1) / coefficient, rubi_subst(&rubi_rhs_int(&transformed_integrand, sub), sub, u__))
        },
    ));
}

fn push_rules_rule_1378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, h__, m_, p_, q_, u__);
    rules.push(rubi_rule!(
        order: 1378,
        source: "Int[(g_.+h_.*u_)^m_.*(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(g+h*x)^m*(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
        FreeQ[{a,c,d,e,f,g,h,m,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * u__).pow(m_)
            * (a__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_),
        with: [a__, c__, d__, e__, f__, g__, h__, u__, m_, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        x_dep: [],
        x_free: [a__, c__, d__, e__, f__, g__, h__, m_, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__, m_, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&g__ + &h__ * &sub_atom).pow(&m_)
                * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_);
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
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
        * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
        * (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) * (d__ + f__ * x_.pow(2)).pow(q_) * (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + c__ * x_.pow(2)).pow(p_) * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_) * (g__ + h__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_)
        * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
        * (d__ + e__ * x_ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_)
        * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
        * (d__ + f__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (g__ + h__ * x_)
        / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (g__ + h__ * x_) / ((a__ + b__ * x_ + c__ * x_.pow(2)) * (d__ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (g__ + h__ * x_)
        / ((a__ + b__ * x_ + c__ * x_.pow(2)).pow(Atom::num(1) / Atom::num(3))
            * (d__ + e__ * x_ + f__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (g__ + h__ * x_) / ((a__ + c__ * x_.pow(2)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (g__ + h__ * x_)
        / ((a__ + c__ * x_.pow(2)).pow(Atom::num(1) / Atom::num(3)) * (d__ + f__ * x_.pow(2)))
}
