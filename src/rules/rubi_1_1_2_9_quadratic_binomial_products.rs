use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    let first_rule = rules.len();
    push_rules_rule_555(rules);
    push_rules_rule_639(rules);
    push_rules_rule_640(rules);
    push_rules_rule_641(rules);
    push_rules_rule_642(rules);
    push_rules_rule_643(rules);
    push_rules_rule_644(rules);
    push_rules_rule_645(rules);
    push_rules_rule_646(rules);
    push_rules_rule_647(rules);
    push_rules_rule_648(rules);
    push_rules_rule_649(rules);
    push_rules_rule_650(rules);
    push_rules_rule_651(rules);
    push_rules_rule_652(rules);
    push_rules_rule_653(rules);
    push_rules_rule_654(rules);
    push_rules_rule_655(rules);
    push_rules_rule_656(rules);
    push_rules_rule_657(rules);
    push_rules_rule_658(rules);
    push_rules_rule_659(rules);
    push_rules_rule_660(rules);
    push_rules_rule_661(rules);
    push_rules_rule_662(rules);
    push_rules_rule_663(rules);
    push_rules_rule_664(rules);
    push_rules_rule_665(rules);
    push_rules_rule_666(rules);
    push_rules_rule_667(rules);
    push_rules_rule_668(rules);
    push_rules_rule_669(rules);
    push_rules_rule_670(rules);
    push_rules_rule_671(rules);
    push_rules_rule_672(rules);
    push_rules_rule_673(rules);
    push_rules_rule_674(rules);
    push_rules_rule_675(rules);
    push_rules_rule_676(rules);
    push_rules_rule_677(rules);
    push_rules_rule_678(rules);
    push_rules_rule_679(rules);
    push_rules_rule_680(rules);
    push_rules_rule_681(rules);
    push_rules_rule_682(rules);
    push_rules_rule_683(rules);
    push_rules_rule_684(rules);
    push_rules_rule_685(rules);
    push_rules_rule_686(rules);
    push_rules_rule_687(rules);
    push_rules_rule_688(rules);
    push_rules_rule_689(rules);
    push_rules_rule_690(rules);
    push_rules_rule_691(rules);
    push_rules_rule_692(rules);
    push_rules_rule_693(rules);
    push_rules_rule_694(rules);
    push_rules_rule_695(rules);
    push_rules_rule_696(rules);
    push_rules_rule_697(rules);
    push_rules_rule_698(rules);
    push_rules_rule_699(rules);
    push_rules_rule_700(rules);
    push_rules_rule_701(rules);
    push_rules_rule_702(rules);
    push_rules_rule_703(rules);
    push_rules_rule_704(rules);
    push_rules_rule_705(rules);
    push_rules_rule_706(rules);
    push_rules_rule_707(rules);
    push_rules_rule_708(rules);
    push_rules_rule_709(rules);
    push_rules_rule_710(rules);
    push_rules_rule_711(rules);
    push_rules_rule_712(rules);
    push_rules_rule_713(rules);
    push_rules_rule_714(rules);
    push_rules_rule_715(rules);
    push_rules_rule_716(rules);
    push_rules_rule_717(rules);
    push_rules_rule_718(rules);
    push_rules_rule_719(rules);
    push_rules_rule_720(rules);
    push_rules_rule_721(rules);
    push_rules_rule_722(rules);
    push_rules_rule_723(rules);
    for rule in &mut rules[first_rule..] {
        rule.require_even_quadratic_binomial_base = true;
    }
}

fn push_rules_rule_555(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 555,
        source: "Int[(f_+g_.*x_)/(Sqrt[x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          2 \\[Star] Subst[Int[(f+g*x^2)/Sqrt[a+c*x^4],x],x,Sqrt[x]] /;
        FreeQ[{a,c,f,g},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_)
            / (x_.pow((1, 2)) * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, f__, g__, x_],
        optional: [c__, g__],
        x_free: [a__, c__, f__, g__],
        when: { freeq!([a__, c__, f__, g__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((&f__ + &g__ * sub_atom.pow(2))
                    / (&a__ + &c__ * sub_atom.pow(4)).sqrt()),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.sqrt());
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_639(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    let rule = rubi_rule!(
        order: 639,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(c+d*x)^(m+p)*(e+f*x)^n*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0] && Not[IntegerQ[m]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [b__, d__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(p_) || gtq!(a__, 0) && gtq!(c__, 0) && !integerq!(m_))
        },
        rhs: {
            rubi_rhs_int(
                &((&c__ + &d__ * x_).pow(&m_ + &p_)
                    * (&e__ + &f__ * x_).pow(&n_)
                    * ((&a__ / &c__) + (&b__ / &d__) * x_).pow(&p_)),
                x_,
            )
        },
    );
    rules.push(rule.with_even_quadratic_binomial_base());
}

fn push_rules_rule_640(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let rule = rubi_rule!(
        order: 640,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (g/e)^n \\[Star] Int[(d+e*x)^(m+n)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[e*f-d*g,0] && IntegerQ[n] && Not[IntegerQ[m] && SimplerQ[f+g*x,d+e*x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && integerq!(n_)
                && !(integerq!(m_)
                    && simplerq!(&f__ + &g__ * x_, &d__ + &e__ * x_))
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &((&d__ + &e__ * x_).pow(&m_ + &n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star((&g__ / &e__).pow(&n_), primitive)
        },
    );
    rules.push(rule.with_even_quadratic_binomial_base());
}

fn push_rules_rule_641(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    let rule = rubi_rule!(
        order: 641,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (e/g)^m \\[Star] Int[(f+g*x)^(m+n)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[e*f-d*g,0] && GtQ[e/g,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && gtq!(&e__ / &g__, 0)
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &((&f__ + &g__ * x_).pow(&m_ + &n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star((&e__ / &g__).pow(&m_), primitive)
        },
    );
    rules.push(rule.with_even_quadratic_binomial_base());
}

fn push_rules_rule_642(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 642,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^m/(f+g*x)^m \\[Star] Int[(f+g*x)^(m+n)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[e*f-d*g,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let primitive = rubi_rhs_int(
                &(second_affine.pow(&m_ + &n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star(first_affine.pow(&m_) / second_affine.pow(&m_), primitive)
        },
    ));
}

fn push_rules_rule_643(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 643,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(c*e+d*f*x^2)^m*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[m,n] && EqQ[d*e+c*f,0] && (IntegerQ[m] || GtQ[c,0] && GtQ[e,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, d__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(m_, n_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && (integerq!(m_) || gtq!(c__, 0) && gtq!(e__, 0))
        },
        rhs: {
            rubi_rhs_int(
                &((&c__ * &e__ + &d__ * &f__ * x_.pow(2)).pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_644(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 644,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2),x_Symbol] :=
          a*x*(c+d*x)^(m+1)*(e+f*x)^(n+1)/(c*e) /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[m,n] && EqQ[d*e+c*f,0] && EqQ[b*c*e-a*d*f*(2*m+3),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, d__, f__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(m_, n_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && eqq!(
                    &b__ * &c__ * &e__
                        - &a__ * &d__ * &f__ * (Atom::num(2) * &m_ + Atom::num(3)),
                    0
                )
        },
        rhs: {
            rubi_simp(&(&a__
                    * x_
                    * (&c__ + &d__ * x_).pow(&m_ + Atom::num(1))
                    * (&e__ + &f__ * x_).pow(&n_ + Atom::num(1))
                    / (&c__ * &e__)), x_)
        },
    ));
}

fn push_rules_rule_645(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 645,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2),x_Symbol] :=
          (b*c*e-a*d*f)*x*(c+d*x)^(m+1)*(e+f*x)^(n+1)/(2*c*d*e*f*(m+1)) -
          (b*c*e-a*d*f*(2*m+3))/(2*c*d*e*f*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*(e+f*x)^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[m,n] && EqQ[d*e+c*f,0] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, d__, f__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(m_, n_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &c__ + &d__ * x_;
            let second_affine = &e__ + &f__ * x_;
            let m_plus_one = &m_ + Atom::num(1);
            let direct = (&b__ * &c__ * &e__ - &a__ * &d__ * &f__)
                * x_
                * first_affine.pow(&m_plus_one)
                * second_affine.pow(&n_ + Atom::num(1))
                / (Atom::num(2) * &c__ * &d__ * &e__ * &f__ * &m_plus_one);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_plus_one)
                    * second_affine.pow(&n_ + Atom::num(1))),
                x_,
            );
            let coefficient = (&b__ * &c__ * &e__
                - &a__ * &d__ * &f__ * (Atom::num(2) * &m_ + Atom::num(3)))
                / (Atom::num(2) * &c__ * &d__ * &e__ * &f__ * &m_plus_one);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_646(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 646,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2),x_Symbol] :=
          b*x*(c+d*x)^(m+1)*(e+f*x)^(n+1)/(d*f*(2*m+3)) -
          (b*c*e-a*d*f*(2*m+3))/(d*f*(2*m+3)) \\[Star] Int[(c+d*x)^m*(e+f*x)^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[m,n] && EqQ[d*e+c*f,0] && Not[LtQ[m,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, x_],
        optional: [a__, b__, d__, f__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(m_, n_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &c__ + &d__ * x_;
            let second_affine = &e__ + &f__ * x_;
            let two_m_plus_three = Atom::num(2) * &m_ + Atom::num(3);
            let direct = &b__
                * x_
                * first_affine.pow(&m_ + Atom::num(1))
                * second_affine.pow(&n_ + Atom::num(1))
                / (&d__ * &f__ * &two_m_plus_three);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * second_affine.pow(&n_)),
                x_,
            );
            let coefficient = (&b__ * &c__ * &e__
                - &a__ * &d__ * &f__ * &two_m_plus_three)
                / (&d__ * &f__ * &two_m_plus_three);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_647(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 647,
        source: "Int[Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]/(a_.+b_.*x_^2),x_Symbol] :=
          d*f/b \\[Star] Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]),x] +
          1/b \\[Star] Int[(b*c*e-a*d*f)/(Sqrt[c+d*x]*Sqrt[e+f*x]*(a+b*x^2)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[d*e+c*f,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt()
            / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, d__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
        },
        rhs: {
            let first_root = (&c__ + &d__ * x_).sqrt();
            let second_root = (&e__ + &f__ * x_).sqrt();
            let first = rubi_rhs_int(&(Atom::num(1) / (&first_root * &second_root)), x_);
            let second = rubi_rhs_int(
                &((&b__ * &c__ * &e__ - &a__ * &d__ * &f__)
                    / (&first_root
                        * &second_root
                        * (&a__ + &b__ * x_.pow(2)))),
                x_,
            );
            rubi_star(&d__ * &f__ / &b__, first)
                    + rubi_star(Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_648(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 648,
        source: "Int[(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^FracPart[m]*(e+f*x)^FracPart[m]/(c*e+d*f*x^2)^FracPart[m] \\[Star] Int[(c*e+d*f*x^2)^m*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[m,n] && EqQ[d*e+c*f,0] && Not[EqQ[p,2] && LtQ[m,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, d__, f__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(m_, n_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && !(eqq!(p_, 2) && ltq!(m_, -1))
        },
        rhs: {
            let first_affine = &c__ + &d__ * x_;
            let second_affine = &e__ + &f__ * x_;
            let frac_m = rubi_frac_part(&m_);
            let primitive = rubi_rhs_int(
                &((&c__ * &e__ + &d__ * &f__ * x_.pow(2)).pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let coefficient = first_affine.pow(&frac_m) * second_affine.pow(&frac_m)
                / (&c__ * &e__ + &d__ * &f__ * x_.pow(2)).pow(&frac_m);
            rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_649(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 649,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          2/e^(n+2*p+1) \\[Star] Subst[Int[x^(2*m+1)*(e*f-d*g+g*x^2)^n*(c*d^2+a*e^2-2*c*d*x^2+c*x^4)^p,x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[p,0] && ILtQ[n,0] && IntegerQ[m+1/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && integerq!(&m_ + Atom::num(1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed = sub.pow(Atom::num(2) * &m_ + Atom::num(1))
                * (&e__ * &f__ - &d__ * &g__ + &g__ * sub.pow(2)).pow(&n_)
                * (&c__ * d__.pow(2) + &a__ * e__.pow(2)
                    - Atom::num(2) * &c__ * &d__ * sub.pow(2)
                    + &c__ * sub.pow(4))
                .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub_symbol);
            let substituted = rubi_subst(
                &primitive,
                sub_symbol,
                (&d__ + &e__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) / e__.pow(&n_ + Atom::num(2) * &p_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_650(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 650,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+c*x^2)^p,d+e*x,x],R=PolynomialRemainder[(a+c*x^2)^p,d+e*x,x]},
          R*(d+e*x)^(m+1)*(f+g*x)^(n+1)/((m+1)*(e*f-d*g)) +
          1/((m+1)*(e*f-d*g)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^n*ExpandToSum[(m+1)*(e*f-d*g)*Qx-g*R*(m+n+2),x],x]] /;
        FreeQ[{a,c,d,e,f,g,n},x] && IGtQ[p,0] && ILtQ[2*m,-2] && Not[IntegerQ[n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_], x_)
                && igtq!(p_, 0)
                && iltq!(Atom::num(2) * &m_, -2)
                && !integerq!(n_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic_power = (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let capital_q = rubi_polynomial_quotient(&quadratic_power, &first_affine, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&quadratic_power, &first_affine, x_).rubi_rhs();
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let denominator = (&m_ + Atom::num(1)) * &ef_dg;
            let direct = &capital_r
                * first_affine.pow(&m_ + Atom::num(1))
                * second_affine.pow(&n_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &((&m_ + Atom::num(1)) * &ef_dg * capital_q
                    - &g__ * &capital_r * (&m_ + &n_ + Atom::num(2))),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * second_affine.pow(&n_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_651(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 651,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          c^p*(d+e*x)^(m+2*p)*(f+g*x)^(n+1)/(g*e^(2*p)*(m+n+2*p+1)) +
          1/(g*e^(2*p)*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(f+g*x)^n*
            ExpandToSum[g*(m+n+2*p+1)*(e^(2*p)*(a+c*x^2)^p-c^p*(d+e*x)^(2*p))-c^p*(e*f-d*g)*(m+2*p)*(d+e*x)^(2*p-1),x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[p,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && NeQ[m+n+2*p+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(p_, 0)
                && !integerq!(m_)
                && !integerq!(n_)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let denominator = &g__ * e__.pow(Atom::num(2) * &p_) * &balance;
            let direct = c__.pow(&p_)
                * first_affine.pow(&m_ + Atom::num(2) * &p_)
                * second_affine.pow(&n_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&g__
                    * &balance
                    * (e__.pow(Atom::num(2) * &p_) * quadratic.pow(&p_)
                        - c__.pow(&p_) * first_affine.pow(Atom::num(2) * &p_))
                    - c__.pow(&p_)
                        * (&e__ * &f__ - &d__ * &g__)
                        * (&m_ + Atom::num(2) * &p_)
                        * first_affine.pow(Atom::num(2) * &p_ - Atom::num(1))),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * second_affine.pow(&n_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_652(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 652,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
        FreeQ[{a,c,d,e,f,g,m,n},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 653,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
          g*(d+e*x)^m/(c*m) +
          1/c \\[Star] Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d+c*e*f)*x,x]/(a+c*x^2),x] /;
        FreeQ[{a,c,d,e,f,g},x] && FractionQ[m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && fractionq!(m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let numerator = rubi_simp(
                &(&c__ * &d__ * &f__ - &a__ * &e__ * &g__
                    + (&g__ * &c__ * &d__ + &c__ * &e__ * &f__) * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1)) * numerator / quadratic),
                x_,
            );
            rubi_simp(&(&g__ * first_affine.pow(&m_) / (&c__ * &m_)), x_)
                    + rubi_star(Atom::num(1) / &c__, primitive)
        },
    ));
}

fn push_rules_rule_654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 654,
        source: "Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
          2 \\[Star] Subst[Int[(e*f-d*g+g*x^2)/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,c,d,e,f,g},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_)
            / ((d__ + e__ * x_).sqrt() * (a__ + c__ * x_.pow(2))),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed = (&e__ * &f__ - &d__ * &g__ + &g__ * sub.pow(2))
                / (&c__ * d__.pow(2) + &a__ * e__.pow(2)
                    - Atom::num(2) * &c__ * &d__ * sub.pow(2)
                    + &c__ * sub.pow(4));
            let primitive = rubi_rhs_int(&transformed, sub_symbol);
            let substituted = rubi_subst(
                &primitive,
                sub_symbol,
                (&d__ + &e__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 655,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) +
          1/(c*d^2+a*e^2) \\[Star] Int[(d+e*x)^(m+1)*Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]/(a+c*x^2),x] /;
        FreeQ[{a,c,d,e,f,g},x] && FractionQ[m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && fractionq!(m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let numerator = rubi_simp(
                &(&c__ * &d__ * &f__ + &a__ * &e__ * &g__
                    - &c__ * (&e__ * &f__ - &d__ * &g__) * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * numerator / quadratic),
                x_,
            );
            rubi_simp(&((&e__ * &f__ - &d__ * &g__)
                    * first_affine.pow(&m_ + Atom::num(1))
                    / ((&m_ + Atom::num(1)) * &invariant)), x_)
                    + rubi_star(Atom::num(1) / invariant, primitive)
        },
    ));
}

fn push_rules_rule_656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 656,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
          With[{q=Denominator[m]},
          q/e \\[Star] Subst[Int[ExpandIntegrand[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n/((c*d^2+a*e^2)/e^2-2*c*d*x^q/e^2+c*x^(2*q)/e^2),x],x],x,(d+e*x)^(1/q)]] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[n] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(n_)
                && fractionq!(m_)
        },
        rhs: {
            let q = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let sub_q = sub.pow(&q);
            let transformed = sub.pow(&q * (&m_ + Atom::num(1)) - Atom::num(1))
                * (((&e__ * &f__ - &d__ * &g__) / &e__ + &g__ * &sub_q / &e__)
                    .pow(&n_)
                    / ((&c__ * d__.pow(2) + &a__ * e__.pow(2)) / e__.pow(2)
                        - Atom::num(2) * &c__ * &d__ * &sub_q / e__.pow(2)
                        + &c__ * sub.pow(Atom::num(2) * &q) / e__.pow(2)));
            let expanded = rubi_expand_integrand(&transformed, sub_symbol);
            let primitive = rubi_rhs_int(&expanded, sub_symbol);
            let substituted = rubi_subst(
                &primitive,
                sub_symbol,
                (&d__ + &e__ * x_).pow(Atom::num(1) / &q),
            );
            rubi_star(&q / &e__, substituted)
        },
    ));
}

fn push_rules_rule_657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 657,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_./(a_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n/(a+c*x^2),x],x] /;
        FreeQ[{a,c,d,e,f,g,m},x] && IntegersQ[n]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_) && integersq!([n_])
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                / (&a__ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 658,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
          g/c \\[Star] Int[Simp[2*e*f+d*g+e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] +
          1/c \\[Star] Int[Simp[c*d*f^2-2*a*e*f*g-a*d*g^2+(c*e*f^2+2*c*d*f*g-a*e*g^2)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+c*x^2),x] /;
        FreeQ[{a,c,d,e,f,g},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let first_numerator = rubi_simp(
                &(Atom::num(2) * &e__ * &f__ + &d__ * &g__ + &e__ * &g__ * x_),
                x_,
            );
            let first = rubi_rhs_int(
                &(first_numerator
                    * first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ - Atom::num(2))),
                x_,
            );
            let second_numerator = rubi_simp(
                &(&c__ * &d__ * f__.pow(2)
                    - Atom::num(2) * &a__ * &e__ * &f__ * &g__
                    - &a__ * &d__ * g__.pow(2)
                    + (&c__ * &e__ * f__.pow(2)
                        + Atom::num(2) * &c__ * &d__ * &f__ * &g__
                        - &a__ * &e__ * g__.pow(2))
                        * x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(second_numerator
                    * first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ - Atom::num(2))
                    / (&a__ + &c__ * x_.pow(2))),
                x_,
            );
            rubi_star(&g__ / &c__, first)
                    + rubi_star(Atom::num(1) / &c__, second)
        },
    ));
}

fn push_rules_rule_659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 659,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
          e*g/c \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] +
          1/c \\[Star] Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+c*x^2),x] /;
        FreeQ[{a,c,d,e,f,g},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let first = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ - Atom::num(1))),
                x_,
            );
            let numerator = rubi_simp(
                &(&c__ * &d__ * &f__ - &a__ * &e__ * &g__
                    + (&c__ * &e__ * &f__ + &c__ * &d__ * &g__) * x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(numerator
                    * first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ - Atom::num(1))
                    / (&a__ + &c__ * x_.pow(2))),
                x_,
            );
            rubi_star(&e__ * &g__ / &c__, first)
                    + rubi_star(Atom::num(1) / &c__, second)
        },
    ));
}

fn push_rules_rule_660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 660,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
          -g*(e*f-d*g)/(c*f^2+a*g^2) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n,x] +
          1/(c*f^2+a*g^2) \\[Star]
            Int[Simp[c*d*f+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+c*x^2),x] /;
        FreeQ[{a,c,d,e,f,g},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && LtQ[n,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let invariant = &c__ * f__.pow(2) + &a__ * g__.pow(2);
            let first = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1)) * second_affine.pow(&n_)),
                x_,
            );
            let numerator = rubi_simp(
                &(&c__ * &d__ * &f__ + &a__ * &e__ * &g__
                    + &c__ * (&e__ * &f__ - &d__ * &g__) * x_),
                x_,
            );
            let second = rubi_rhs_int(
                &(numerator
                    * first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ + Atom::num(1))
                    / (&a__ + &c__ * x_.pow(2))),
                x_,
            );
            rubi_star(-&g__ * (&e__ * &f__ - &d__ * &g__) / &invariant, first) + rubi_star(Atom::num(1) / invariant, second)
        },
    ));
}

fn push_rules_rule_661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 661,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*(a_.+c_.*x_^2)),x_Symbol] :=
          Int[ExpandIntegrand[1/(Sqrt[d+e*x]*Sqrt[f+g*x]),(d+e*x)^(m+1/2)/(a+c*x^2),x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[m+1/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            / ((f__ + g__ * x_).sqrt() * (a__ + c__ * x_.pow(2))),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(&m_ + Atom::num(1) / 2, 0)
        },
        rhs: {
            let first = Atom::num(1)
                / ((&d__ + &e__ * x_).sqrt()
                    * (&f__ + &g__ * x_).sqrt());
            let second = (&d__ + &e__ * x_)
                .pow(&m_ + Atom::num(1) / 2)
                / (&a__ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 662,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+c*x^2),x],x] /;
        FreeQ[{a,c,d,e,f,g,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let first = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_);
            let second = Atom::num(1) / (&a__ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 663,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{q=Rt[-a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(-q+c*x)^p*(q+c*x)^p,x],x] /;
         Not[FractionalPowerFactorQ[q]]] /;
        FreeQ[{a,c,d,e,f,g},x] && ILtQ[p,-1] && IntegersQ[m,n] && NiceSqrtQ[-a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && iltq!(p_, -1)
                && integersq!([m_, n_])
                && rubi_nice_sqrt_q(&(-&a__ * &c__))
                && !rubi_fractional_power_factor_q(&q)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (-&q + &c__ * x_).pow(&p_)
                * (&q + &c__ * x_).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            let primitive = rubi_rhs_int(&expanded, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), primitive)
        },
    ));
}

fn push_rules_rule_664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 664,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^2*(a_.+c_.*x_^2)^p_.,x_Symbol] :=
          g^2*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[d*g*(p+1)-e*f*(m+2*p+3),0] &&
          EqQ[e*(c*f^2+a*g^2)*(m+1)+2*c*f*(e*f-d*g)*(p+1),0] && NeQ[m+2*p+3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(2)
            * (a__ + c__ * x_.pow(2)).pow(p_),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, c__, d__, e__, f__, g__, m_, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(
                    &d__ * &g__ * (&p_ + Atom::num(1))
                        - &e__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                    0
                )
                && eqq!(
                    &e__
                        * (&c__ * f__.pow(2) + &a__ * g__.pow(2))
                        * (&m_ + Atom::num(1))
                        + Atom::num(2)
                            * &c__
                            * &f__
                            * (&e__ * &f__ - &d__ * &g__)
                            * (&p_ + Atom::num(1)),
                    0
                )
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
        },
        rhs: {
            rubi_simp(&(g__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (&c__
                        * &e__
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))), x_)
        },
    ));
}

fn push_rules_rule_665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 665,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_./(a_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2^(m-1)*d^(m-2)*(e*f+d*g)^n*(d+e*x)/(c*e^(n-1)*Sqrt[a+c*x^2]) +
          1/(c*e^(n-2)) \\[Star] Int[ExpandToSum[(2^(m-1)*d^(m-1)*(e*f+d*g)^n-e^n*(d+e*x)^(m-1)*(f+g*x)^n)/(d-e*x),x]/Sqrt[a+c*x^2],x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_)
            / (a__ + c__ * x_.pow(2)).pow((3, 2)),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [c__, d__, e__, f__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic_root = (&a__ + &c__ * x_.pow(2)).sqrt();
            let direct = -Atom::num(2).pow(&m_ - Atom::num(1))
                * d__.pow(&m_ - Atom::num(2))
                * (&e__ * &f__ + &d__ * &g__).pow(&n_)
                * &first_affine
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &quadratic_root);
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(&m_ - Atom::num(1))
                    * d__.pow(&m_ - Atom::num(1))
                    * (&e__ * &f__ + &d__ * &g__).pow(&n_)
                    - e__.pow(&n_)
                        * first_affine.pow(&m_ - Atom::num(1))
                        * second_affine.pow(&n_))
                    / (&d__ - &e__ * x_)),
                x_,
            );
            let primitive = rubi_rhs_int(&(payload / quadratic_root), x_);
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&c__ * e__.pow(&n_ - Atom::num(2))), primitive)
        },
    ));
}

fn push_rules_rule_666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 666,
        source: "Int[x_^n_.*(d_.+e_.*x_)^m_./(a_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2^(m-1)*d^(m+n-2)*(d+e*x)/(c*e^(n-1)*Sqrt[a+c*x^2]) +
          d^2/a \\[Star] Int[ExpandToSum[((d+e*x)^(m-1)-2^(m-1)*d^(m+n-1)*e^(-n)*x^(-n))/(d-e*x),x]/(x^(-n)*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && IGtQ[m,0] && ILtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(n_) * (d__ + e__ * x_).pow(m_)
            / (a__ + c__ * x_.pow(2)).pow((3, 2)),
        with: [a__, c__, d__, e__, m_, n_, x_],
        optional: [c__, d__, e__, m_, n_],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic_root = (&a__ + &c__ * x_.pow(2)).sqrt();
            let direct = -Atom::num(2).pow(&m_ - Atom::num(1))
                * d__.pow(&m_ + &n_ - Atom::num(2))
                * &first_affine
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &quadratic_root);
            let payload = rubi_expand_to_sum(
                &((first_affine.pow(&m_ - Atom::num(1))
                    - Atom::num(2).pow(&m_ - Atom::num(1))
                        * d__.pow(&m_ + &n_ - Atom::num(1))
                        * e__.pow(-&n_)
                        * x_.pow(-&n_))
                    / (&d__ - &e__ * x_)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(payload / (x_.pow(-&n_) * quadratic_root)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(d__.pow(2) / &a__, primitive)
        },
    ));
}

fn push_rules_rule_667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 667,
        source: "Int[(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          Int[(a/d+c*x/e)*(f+g*x)^n*(a+c*x^2)^(p-1),x] /;
        FreeQ[{a,c,d,e,f,g,n,p},x] && EqQ[c*d^2+a*e^2,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [c__, e__, f__, g__, n_],
        x_free: [a__, c__, d__, e__, f__, g__, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            rubi_rhs_int(
                &((&a__ / &d__ + &c__ * x_ / &e__)
                    * (&f__ + &g__ * x_).pow(&n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ - Atom::num(1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 668,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[c*e*f*(m+2*p+2)+c*d*g*m,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(
                    &c__ * &e__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2))
                        + &c__ * &d__ * &g__ * &m_,
                    0
                )
        },
        rhs: {
            rubi_simp(&(&g__
                    * (&d__ + &e__ * x_).pow(&m_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (&c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2)))), x_)
        },
    ));
}

fn push_rules_rule_669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 669,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) -
          e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &c__ * &d__ * (&p_ + Atom::num(1));
            let direct = (&d__ * &g__ + &e__ * &f__)
                * first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))),
                x_,
            );
            let coefficient = &e__
                * (&m_ * (&d__ * &g__ + &e__ * &f__)
                    + Atom::num(2) * &e__ * &f__ * (&p_ + Atom::num(1)))
                / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 670,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) -
          e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1)) \\[Star] Int[(d+e*x)^Simplify[m-1]*(a+c*x^2)^Simplify[p+1],x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NeQ[p,-1] && Not[IGtQ[m,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && sum_simplerq!(p_, 1)
                && sum_simplerq!(m_, -1)
                && neq!(p_, -1)
                && !igtq!(m_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &c__ * &d__ * (&p_ + Atom::num(1));
            let direct = (&d__ * &g__ + &e__ * &f__)
                * first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_affine.pow(rubi_simplify(&(&m_ - Atom::num(1))))
                    * quadratic.pow(rubi_simplify(&(&p_ + Atom::num(1))))),
                x_,
            );
            let coefficient = &e__
                * (&m_ * (&d__ * &g__ + &e__ * &f__)
                    + Atom::num(2) * &e__ * &f__ * (&p_ + Atom::num(1)))
                / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 671,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d*g-e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) +
          (m*(g*c*d+c*e*f)+2*e*c*f*(p+1))/(e*(2*c*d)*(m+p+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] &&
          (LtQ[m,-1] && Not[IGtQ[m+p+1,0]] || LtQ[m,0] && LtQ[p,-1] || EqQ[m+2*p+2,0]) && NeQ[m+p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && (ltq!(m_, -1) && !igtq!(&m_ + &p_ + Atom::num(1), 0)
                    || ltq!(m_, 0) && ltq!(p_, -1)
                    || eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0))
                && neq!(&m_ + &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + &p_ + Atom::num(1);
            let direct = (&d__ * &g__ - &e__ * &f__)
                * first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &c__ * &d__ * &balance);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = (&m_ * (&g__ * &c__ * &d__ + &c__ * &e__ * &f__)
                + Atom::num(2) * &e__ * &c__ * &f__ * (&p_ + Atom::num(1)))
                / (&e__ * Atom::num(2) * &c__ * &d__ * &balance);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 672,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) +
          (m*(d*g+e*f)+2*e*f*(p+1))/(e*(m+2*p+2)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && NeQ[m+2*p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let direct = &g__ * first_affine.pow(&m_) * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * &balance);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = (&m_ * (&d__ * &g__ + &e__ * &f__)
                + Atom::num(2) * &e__ * &f__ * (&p_ + Atom::num(1)))
                / (&e__ * &balance);
            rubi_simp(&(direct), x_) + rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_673(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 673,
        source: "Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          ((e*f+d*g)*(2*p+3)+2*e*g*(p+1)*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+3)) /;
        FreeQ[{a,c,d,e,f,g,p},x] && EqQ[a*e*g-c*d*f*(2*p+3),0] && NeQ[p,-1]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(
                    &a__ * &e__ * &g__
                        - &c__ * &d__ * &f__ * (Atom::num(2) * &p_ + Atom::num(3)),
                    0
                )
                && neq!(p_, -1)
        },
        rhs: {
            rubi_simp(&(((&e__ * &f__ + &d__ * &g__) * (Atom::num(2) * &p_ + Atom::num(3))
                    + Atom::num(2) * &e__ * &g__ * (&p_ + Atom::num(1)) * x_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (Atom::num(2)
                        * &c__
                        * (&p_ + Atom::num(1))
                        * (Atom::num(2) * &p_ + Atom::num(3)))), x_)
        },
    ));
}

fn push_rules_rule_674(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 674,
        source: "Int[x_*(d_+e_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)) -
          e/(2*c*(p+1)) \\[Star] Int[(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e},x] && LtQ[p,-1] && Not[IntegerQ[p] && NiceSqrtQ[-a*c]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_ * (d__ + e__ * x_) * (a__ + c__ * x_.pow(2)).pow(p_),
        with: [a__, c__, d__, e__, p_, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && ltq!(p_, -1)
                && !(integerq!(p_) && rubi_nice_sqrt_q(&(-&a__ * &c__)))
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &c__ * (&p_ + Atom::num(1));
            let direct = (&d__ + &e__ * x_) * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let primitive = rubi_rhs_int(&quadratic.pow(&p_ + Atom::num(1)), x_);
            rubi_simp(&(direct), x_) - rubi_star(&e__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_675(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 675,
        source: "Int[(d_+e_.*x_)*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          a*(e*f+d*g)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) -
          (c*d*f-a*e*g)*x*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) -
          (a*e*g-c*d*f*(2*p+3))/(2*a*c*(p+1)) \\[Star] Int[(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && LtQ[p,-1] && Not[IntegerQ[p] && NiceSqrtQ[-a*c]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, p_, x_],
        optional: [c__, e__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && !(integerq!(p_) && rubi_nice_sqrt_q(&(-&a__ * &c__)))
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let direct = &a__
                * (&e__ * &f__ + &d__ * &g__)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator
                - (&c__ * &d__ * &f__ - &a__ * &e__ * &g__)
                    * x_
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &denominator;
            let primitive = rubi_rhs_int(&quadratic.pow(&p_ + Atom::num(1)), x_);
            let coefficient = (&a__ * &e__ * &g__
                - &c__ * &d__ * &f__ * (Atom::num(2) * &p_ + Atom::num(3)))
                / denominator;
            direct - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_676(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 676,
        source: "Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (e*f+d*g)*(a+c*x^2)^(p+1)/(2*c*(p+1)) +
          e*g*x*(a+c*x^2)^(p+1)/(c*(2*p+3)) -
          (a*e*g-c*d*f*(2*p+3))/(c*(2*p+3)) \\[Star] Int[(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,p},x] && Not[LeQ[p,-1]]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, c__, d__, e__, f__, g__, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_) && !leq!(p_, -1)
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let direct = (&e__ * &f__ + &d__ * &g__)
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                + &e__
                    * &g__
                    * x_
                    * quadratic.pow(&p_ + Atom::num(1))
                    / (&c__ * (Atom::num(2) * &p_ + Atom::num(3)));
            let primitive = rubi_rhs_int(&quadratic.pow(&p_), x_);
            let coefficient = (&a__ * &e__ * &g__
                - &c__ * &d__ * &f__ * (Atom::num(2) * &p_ + Atom::num(3)))
                / (&c__ * (Atom::num(2) * &p_ + Atom::num(3)));
            direct - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_677(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 677,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[Simplify[m+2*p+3],0] && EqQ[c*d*f+a*e*g,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && eqq!(&c__ * &d__ * &f__ + &a__ * &e__ * &g__, 0)
        },
        rhs: {
            rubi_simp(&(-(&e__ * &f__ - &d__ * &g__)
                    * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (Atom::num(2)
                        * (&p_ + Atom::num(1))
                        * (&c__ * d__.pow(2) + &a__ * e__.pow(2)))), x_)
        },
    ));
}

fn push_rules_rule_678(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 678,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) -
          m*(c*d*f+a*e*g)/(2*a*c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[Simplify[m+2*p+3],0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let direct = first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * (&a__ * &g__ - &c__ * &f__ * x_)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))),
                x_,
            );
            let coefficient = &m_ * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__)
                / denominator;
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_679(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 679,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) +
          (c*d*f+a*e*g)/(c*d^2+a*e^2) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[Simplify[m+2*p+3],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let direct = -(&e__ * &f__ - &d__ * &g__)
                * first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * (&p_ + Atom::num(1)) * &invariant);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star((&c__ * &d__ * &f__ + &a__ * &e__ * &g__) / invariant, primitive)
        },
    ));
}

fn push_rules_rule_680(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 680,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          -(d+e*x)^(m+1)*(a+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2))*
            ((d*g-e*f*(m+2))*(c*d^2+a*e^2)-2*c*d^2*p*(e*f-d*g)-e*(g*(m+1)*(c*d^2+a*e^2)+2*c*d*p*(e*f-d*g))*x) -
          p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1)*
            Simp[2*a*c*e*(e*f-d*g)*(m+2)-c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-2*a*e^2*g*(m+1))*x,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && GtQ[p,0] && LtQ[m,-2] && LtQ[m+2*p,0] && Not[ILtQ[m+2*p+3,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -2)
                && ltq!(&m_ + Atom::num(2) * &p_, 0)
                && !iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = e__.pow(2)
                * (&m_ + Atom::num(1))
                * (&m_ + Atom::num(2))
                * &invariant;
            let direct_payload = (&d__ * &g__ - &e__ * &f__ * (&m_ + Atom::num(2)))
                * &invariant
                - Atom::num(2)
                    * &c__
                    * d__.pow(2)
                    * &p_
                    * (&e__ * &f__ - &d__ * &g__)
                - &e__
                    * (&g__ * (&m_ + Atom::num(1)) * &invariant
                        + Atom::num(2)
                            * &c__
                            * &d__
                            * &p_
                            * (&e__ * &f__ - &d__ * &g__))
                    * x_;
            let direct = -first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_)
                * direct_payload
                / &denominator;
            let recursive_payload = rubi_simp(
                &(Atom::num(2)
                    * &a__
                    * &c__
                    * &e__
                    * (&e__ * &f__ - &d__ * &g__)
                    * (&m_ + Atom::num(2))
                    - &c__
                        * (Atom::num(2)
                            * &c__
                            * &d__
                            * (&d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(1))
                                - &e__
                                    * &f__
                                    * (&m_ + Atom::num(2) * &p_ + Atom::num(2)))
                            - Atom::num(2)
                                * &a__
                                * e__.pow(2)
                                * &g__
                                * (&m_ + Atom::num(1)))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(2))
                    * quadratic.pow(&p_ - Atom::num(1))
                    * recursive_payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(&p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_681(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 681,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) +
          p/(e^2*(m+1)*(m+2*p+2)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1)*
            Simp[g*(2*a*e+2*a*e*m)+(g*(2*c*d+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
        FreeQ[{a,c,d,e,f,g,m},x] && GtQ[p,0] &&
          (LtQ[m,-1] || EqQ[p,1] || IntegerQ[p] && Not[RationalQ[m]]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_)
                && gtq!(p_, 0)
                && (ltq!(m_, -1) || eqq!(p_, 1) || integerq!(p_) && !rationalq!(m_))
                && neq!(m_, -1)
                && !iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let denominator = e__.pow(2) * (&m_ + Atom::num(1)) * &balance;
            let direct = first_affine.pow(&m_ + Atom::num(1))
                * (&e__ * &f__ * &balance
                    - &d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(1))
                    + &e__ * &g__ * (&m_ + Atom::num(1)) * x_)
                * quadratic.pow(&p_)
                / &denominator;
            let payload = rubi_simp(
                &(&g__ * (Atom::num(2) * &a__ * &e__ + Atom::num(2) * &a__ * &e__ * &m_)
                    + (&g__ * (Atom::num(2) * &c__ * &d__ + Atom::num(4) * &c__ * &d__ * &p_)
                        - Atom::num(2) * &c__ * &e__ * &f__ * &balance)
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ - Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_682(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 682,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*c*d*(2*p+1)+g*c*e*(m+2*p+1)*x)*(a+c*x^2)^p/
            (c*e^2*(m+2*p+1)*(m+2*p+2)) +
          2*p/(c*e^2*(m+2*p+1)*(m+2*p+2)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^(p-1)*
            Simp[f*a*c*e^2*(m+2*p+2)+a*c*d*e*g*m-(c^2*f*d*e*(m+2*p+2)-g*(c^2*d^2*(2*p+1)+a*c*e^2*(m+2*p+1)))*x,x],x] /;
        FreeQ[{a,c,d,e,f,g,m},x] &&
          GtQ[p,0] && (IntegerQ[p] || Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,0]) && Not[ILtQ[m+2*p,0]] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_)
                && gtq!(p_, 0)
                && (integerq!(p_)
                    || !rationalq!(m_)
                    || geq!(m_, -1) && ltq!(m_, 0))
                && !iltq!(&m_ + Atom::num(2) * &p_, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance1 = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let balance2 = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let denominator = &c__ * e__.pow(2) * &balance1 * &balance2;
            let direct = first_affine.pow(&m_ + Atom::num(1))
                * (&c__ * &e__ * &f__ * &balance2
                    - &g__ * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(1))
                    + &g__ * &c__ * &e__ * &balance1 * x_)
                * quadratic.pow(&p_)
                / &denominator;
            let payload = rubi_simp(
                &(&f__ * &a__ * &c__ * e__.pow(2) * &balance2
                    + &a__ * &c__ * &d__ * &e__ * &g__ * &m_
                    - (&c__ * &c__ * &f__ * &d__ * &e__ * &balance2
                        - &g__
                            * (&c__ * &c__ * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(1))
                                + &a__ * &c__ * e__.pow(2) * &balance1))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * quadratic.pow(&p_ - Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_683(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 683,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(a+c*x^2)^p*ExpandIntegrand[(d+e*x)^m*(f+g*x),x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && ILtQ[p,-1] && IGtQ[m,0] && RationalQ[a,c,d,e,f,g]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, e__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && iltq!(p_, -1)
                && igtq!(m_, 0)
                && rationalq!([a__, c__, d__, e__, f__, g__])
        },
        rhs: {
            let affine_product = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_);
            let expanded = rubi_expand_integrand(&affine_product, x_);
            rubi_rhs_int(
                &((&a__ + &c__ * x_.pow(2)).pow(&p_) * expanded),
                x_,
            )
        },
    ));
}

fn push_rules_rule_684(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 684,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m-1)*(a+c*x^2)^(p+1)*(a*(e*f+d*g)-(c*d*f-a*e*g)*x)/(2*a*c*(p+1)) -
          1/(2*a*c*(p+1)) \\[Star] Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1)*
            Simp[a*e*(e*f*(m-1)+d*g*m)-c*d^2*f*(2*p+3)+e*(a*e*g*m-c*d*f*(m+2*p+2))*x,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && LtQ[p,-1] && GtQ[m,1] &&
          (EqQ[d,0] || EqQ[m,2] && EqQ[p,-3] && RationalQ[a,c,d,e,f,g] || Not[ILtQ[m+2*p+3,0]])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && (eqq!(d__, 0)
                    || eqq!(m_, 2)
                        && eqq!(p_, -3)
                        && rationalq!([a__, c__, d__, e__, f__, g__])
                    || !iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let direct = first_affine.pow(&m_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                * (&a__ * (&e__ * &f__ + &d__ * &g__)
                    - (&c__ * &d__ * &f__ - &a__ * &e__ * &g__) * x_)
                / &denominator;
            let payload = rubi_simp(
                &(&a__
                    * &e__
                    * (&e__ * &f__ * (&m_ - Atom::num(1)) + &d__ * &g__ * &m_)
                    - &c__ * d__.pow(2) * &f__ * (Atom::num(2) * &p_ + Atom::num(3))
                    + &e__
                        * (&a__ * &e__ * &g__ * &m_
                            - &c__ * &d__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2)))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(2))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_685(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 685,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) -
          1/(2*a*c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*Simp[a*e*g*m-c*d*f*(2*p+3)-c*e*f*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && LtQ[p,-1] && GtQ[m,0] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let direct = first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * (&a__ * &g__ - &c__ * &f__ * x_)
                / &denominator;
            let payload = rubi_simp(
                &(&a__ * &e__ * &g__ * &m_
                    - &c__ * &d__ * &f__ * (Atom::num(2) * &p_ + Atom::num(3))
                    - &c__
                        * &e__
                        * &f__
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_686(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 686,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -(d+e*x)^(m+1)*(f*a*c*e-a*g*c*d+c*(c*d*f+a*e*g)*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)*(c*d^2+a*e^2)) +
          1/(2*a*c*(p+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
            Simp[f*(c^2*d^2*(2*p+3)+a*c*e^2*(m+2*p+3))-a*c*d*e*g*m+c*e*(c*d*f+a*e*g)*(m+2*p+4)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && LtQ[p,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = Atom::num(2)
                * &a__
                * &c__
                * (&p_ + Atom::num(1))
                * &invariant;
            let direct = -first_affine.pow(&m_ + Atom::num(1))
                * (&f__ * &a__ * &c__ * &e__ - &a__ * &g__ * &c__ * &d__
                    + &c__ * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__) * x_)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_simp(
                &(&f__
                    * (&c__ * &c__ * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(3))
                        + &a__
                            * &c__
                            * e__.pow(2)
                            * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                    - &a__ * &c__ * &d__ * &e__ * &g__ * &m_
                    + &c__
                        * &e__
                        * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * quadratic.pow(&p_ + Atom::num(1)) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_687(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 687,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) +
          1/(c*(m+2*p+2)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^p*
            Simp[c*d*f*(m+2*p+2)-a*e*g*m+c*(e*f*(m+2*p+2)+d*g*m)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g,p},x] && GtQ[m,0] && NeQ[m+2*p+2,0] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p]) && Not[IGtQ[m,0] && EqQ[f,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_)
                && gtq!(m_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
                && !(igtq!(m_, 0) && eqq!(f__, 0))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let denominator = &c__ * &balance;
            let direct = &g__ * first_affine.pow(&m_) * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_simp(
                &(&c__ * &d__ * &f__ * &balance - &a__ * &e__ * &g__ * &m_
                    + &c__ * (&e__ * &f__ * &balance + &d__ * &g__ * &m_) * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_688(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 688,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) +
          1/((m+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g,p},x] && LtQ[m,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_)
                && ltq!(m_, -1)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = (&e__ * &f__ - &d__ * &g__)
                * first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_simp(
                &((&c__ * &d__ * &f__ + &a__ * &e__ * &g__) * (&m_ + Atom::num(1))
                    - &c__
                        * (&e__ * &f__ - &d__ * &g__)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_689(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 689,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) +
          1/((m+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && ILtQ[Simplify[m+2*p+3],0] && NeQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && iltq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = (&e__ * &f__ - &d__ * &g__)
                * first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_simp(
                &((&c__ * &d__ * &f__ + &a__ * &e__ * &g__) * (&m_ + Atom::num(1))
                    - &c__
                        * (&e__ * &f__ - &d__ * &g__)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_690(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 690,
        source: "Int[(f_+g_.*x_)/(Sqrt[e_*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          Sqrt[x]/Sqrt[e*x] \\[Star] Int[(f+g*x)/(Sqrt[x]*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,e,f,g},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ + g__ * x_)
            / ((e__ * x_).sqrt() * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, e__, f__, g__, x_],
        optional: [c__, g__],
        x_free: [a__, c__, e__, f__, g__],
        when: { freeq!([a__, c__, e__, f__, g__], x_) },
        rhs: {
            let primitive = rubi_rhs_int(
                &((&f__ + &g__ * x_)
                    / (x_.sqrt() * (&a__ + &c__ * x_.pow(2)).sqrt())),
                x_,
            );
            rubi_star(x_.sqrt() / (&e__ * x_).sqrt(), primitive)
        },
    ));
}

fn push_rules_rule_691(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 691,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a*e+c*d*x,x], R=PolynomialRemainder[(f+g*x)^n,a*e+c*d*x,x]},
          -d*R*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) +
          d/(2*a*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*ExpandToSum[2*a*e*(p+1)*Q+R*(m+2*p+2),x],x]] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[n,1] && IGtQ[m,0] && LtQ[p,-1] && EqQ[c*d^2+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && igtq!(m_, 0)
                && ltq!(p_, -1)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let divisor = &a__ * &e__ + &c__ * &d__ * x_;
            let second_power = second_affine.pow(&n_);
            let capital_q = rubi_polynomial_quotient(&second_power, &divisor, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&second_power, &divisor, x_).rubi_rhs();
            let direct = -&d__
                * &capital_r
                * first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &a__ * &e__ * (&p_ + Atom::num(1)));
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &e__ * (&p_ + Atom::num(1)) * capital_q
                    + &capital_r * (&m_ + Atom::num(2) * &p_ + Atom::num(2))),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(&d__ / (Atom::num(2) * &a__ * (&p_ + Atom::num(1))), primitive)
        },
    ));
}

fn push_rules_rule_692(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 692,
        source: "Int[(f_.+g_.*x_)^n_.*(a_.+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          d*(f+g*x)^n*(a+c*x^2)^(p+1)/(2*a*e*p*(d+e*x)) -
          n*(e*f+d*g)/(2*d*e*p) \\[Star] Int[(f+g*x)^(n-1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && IGtQ[n,1] && LtQ[p,-1] && EqQ[n+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, c__, e__, f__, g__, n_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && eqq!(&n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator_affine = &d__ + &e__ * x_;
            let direct = &d__
                * second_affine.pow(&n_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &a__ * &e__ * &p_ * &denominator_affine);
            let primitive = rubi_rhs_int(
                &(second_affine.pow(&n_ - Atom::num(1)) * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &n_ * (&e__ * &f__ + &d__ * &g__)
                / (Atom::num(2) * &d__ * &e__ * &p_);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_693(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 693,
        source: "Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          -(e*f-d*g)*(f+g*x)^(n-1)*(a+c*x^2)^(p+1)/(2*c*d*p*(d+e*x)) +
          1/(2*d*e^2*p) \\[Star] Int[(f+g*x)^(n-2)*(a+c*x^2)^p*Simp[(e*f-d*g)*(e*f+d*g-d*g*n)+2*e^2*f^2*p+e*g*((e*f-d*g)*n+2*e*f*p)*x,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && EqQ[c*d^2+a*e^2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator_affine = &d__ + &e__ * x_;
            let direct = -(&e__ * &f__ - &d__ * &g__)
                * second_affine.pow(&n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &c__ * &d__ * &p_ * &denominator_affine);
            let payload = rubi_simp(
                &((&e__ * &f__ - &d__ * &g__)
                    * (&e__ * &f__ + &d__ * &g__ - &d__ * &g__ * &n_)
                    + Atom::num(2) * e__.pow(2) * f__.pow(2) * &p_
                    + &e__
                        * &g__
                        * ((&e__ * &f__ - &d__ * &g__) * &n_
                            + Atom::num(2) * &e__ * &f__ * &p_)
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(second_affine.pow(&n_ - Atom::num(2)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &d__ * e__.pow(2) * &p_), primitive)
        },
    ));
}

fn push_rules_rule_694(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 694,
        source: "Int[(f_.+g_.*x_)^n_*(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -(e*f-d*g)^n*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*e^(n-1)*(m+p+1)) +
          1/(2*d*e^n*(m+p+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p*
            ExpandToSum[(2*d*e^n*(m+p+1)*(f+g*x)^n-(e*f-d*g)^n*(d*m-e*(m+2*p+2)*x))/(d+e*x),x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[n,1] && ILtQ[m,-1] && LtQ[p,-1] && EqQ[c*d^2+a*e^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (f__ + g__ * x_).pow(n_)
            * (d__ + e__ * x_).pow(m_)
            * (a__ + c__ * x_.pow(2)).pow(p_),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && iltq!(m_, -1)
                && ltq!(p_, -1)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ + &p_ + Atom::num(1);
            let direct = -(&e__ * &f__ - &d__ * &g__).pow(&n_)
                * first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &c__ * &d__ * e__.pow(&n_ - Atom::num(1)) * &balance);
            let payload = rubi_expand_to_sum(
                &((Atom::num(2)
                    * &d__
                    * e__.pow(&n_)
                    * &balance
                    * second_affine.pow(&n_)
                    - (&e__ * &f__ - &d__ * &g__).pow(&n_)
                        * (&d__ * &m_
                            - &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2)) * x_))
                    / &first_affine),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &d__ * e__.pow(&n_) * &balance), primitive)
        },
    ));
}

fn push_rules_rule_695(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 695,
        source: "Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          d*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(2*a*p*(e*f-d*g)*(d+e*x)) +
          1/(p*(2*c*d)*(e*f-d*g)) \\[Star] Int[(f+g*x)^n*(a+c*x^2)^p*(c*e*f*(2*p+1)-c*d*g*(n+2*p+1)+c*e*g*(n+2*p+2)*x),x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && ILtQ[n,0] && ILtQ[n+2*p,0] && Not[IGtQ[n,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(n_, 0)
                && iltq!(&n_ + Atom::num(2) * &p_, 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator_affine = &d__ + &e__ * x_;
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let direct = &d__
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (Atom::num(2) * &a__ * &p_ * &ef_dg * &denominator_affine);
            let primitive = rubi_rhs_int(
                &(second_affine.pow(&n_)
                    * quadratic.pow(&p_)
                    * (&c__ * &e__ * &f__ * (Atom::num(2) * &p_ + Atom::num(1))
                        - &c__ * &d__ * &g__ * (&n_ + Atom::num(2) * &p_ + Atom::num(1))
                        + &c__
                            * &e__
                            * &g__
                            * (&n_ + Atom::num(2) * &p_ + Atom::num(2))
                            * x_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&p_ * Atom::num(2) * &c__ * &d__ * &ef_dg), primitive)
        },
    ));
}

fn push_rules_rule_696(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 696,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && EqQ[e*f+d*g,0] && NeQ[m-n-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
        },
        rhs: {
            rubi_simp(&(-&e__
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(1))
                    * (&f__ + &g__ * x_).pow(&n_)
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (&c__ * (&m_ - &n_ - Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_697(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 697,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(n+1)*(e*f+d*g)) /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && EqQ[m-n-2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && eqq!(&m_ - &n_ - Atom::num(2), 0)
        },
        rhs: {
            rubi_simp(&(-e__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(1))
                    * (&f__ + &g__ * x_).pow(&n_ + Atom::num(1))
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (&c__ * (&n_ + Atom::num(1)) * (&e__ * &f__ + &d__ * &g__))), x_)
        },
    ));
}

fn push_rules_rule_698(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 698,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(n+1)) +
          c*m/(e*g*(n+1)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+c*x^2)^(p-1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && GtQ[p,0] && LtQ[n,-1] && Not[IntegerQ[n+p] && LeQ[n+p+2,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(p_, 0)
                && ltq!(n_, -1)
                && !(integerq!(&n_ + &p_) && leq!(&n_ + &p_ + Atom::num(2), 0))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let direct = first_affine.pow(&m_)
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_)
                / (&g__ * (&n_ + Atom::num(1)));
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * second_affine.pow(&n_ + Atom::num(1))
                    * quadratic.pow(&p_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(&c__ * &m_ / (&e__ * &g__ * (&n_ + Atom::num(1))), primitive)
        },
    ));
}

fn push_rules_rule_699(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 699,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(m-n-1)) -
          c*m*(e*f+d*g)/(e^2*g*(m-n-1)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+c*x^2)^(p-1),x] /;
        FreeQ[{a,c,d,e,f,g,n},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && GtQ[p,0] && NeQ[m-n-1,0] && Not[IGtQ[n,0]] && Not[IntegerQ[n+p] && LtQ[n+p+2,0]] && RationalQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
                && !igtq!(n_, 0)
                && !(integerq!(&n_ + &p_) && ltq!(&n_ + &p_ + Atom::num(2), 0))
                && rationalq!(n_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ - &n_ - Atom::num(1);
            let direct = -first_affine.pow(&m_)
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_)
                / (&g__ * &balance);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * second_affine.pow(&n_)
                    * quadratic.pow(&p_ - Atom::num(1))),
                x_,
            );
            let coefficient = &c__ * &m_ * (&e__ * &f__ + &d__ * &g__)
                / (e__.pow(2) * &g__ * &balance);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_700(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 700,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(p+1)) -
          e*g*n/(c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && LtQ[p,-1] && GtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = &c__ * (&p_ + Atom::num(1));
            let direct = &e__
                * first_affine.pow(&m_ - Atom::num(1))
                * second_affine.pow(&n_)
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(&e__ * &g__ * &n_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_701(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 701,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(p+1)*(e*f+d*g)) +
          e^2*g*(m-n-2)/(c*(p+1)*(e*f+d*g)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1),x] /;
        FreeQ[{a,c,d,e,f,g,n},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && LtQ[p,-1] && RationalQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(p_, -1)
                && rationalq!(n_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let denominator = &c__ * (&p_ + Atom::num(1)) * (&e__ * &f__ + &d__ * &g__);
            let direct = e__.pow(2)
                * first_affine.pow(&m_ - Atom::num(1))
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_)
                    * quadratic.pow(&p_ + Atom::num(1))),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(e__.pow(2) * &g__ * (&m_ - &n_ - Atom::num(2)) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 702,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) -
          n*(e*f+d*g)/(e*(m-n-1)) \\[Star] Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && GtQ[n,0] && NeQ[m-n-1,0] && (IntegerQ[2*p] || IntegerQ[n])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(n_, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
                && (integerq!(Atom::num(2) * &p_) || integerq!(n_))
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &m_ - &n_ - Atom::num(1);
            let direct = -&e__
                * first_affine.pow(&m_ - Atom::num(1))
                * second_affine.pow(&n_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * &balance);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * second_affine.pow(&n_ - Atom::num(1))
                    * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(&n_ * (&e__ * &f__ + &d__ * &g__) / (&e__ * &balance), primitive)
        },
    ));
}

fn push_rules_rule_703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 703,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g)) -
          e*(m-n-2)/((n+1)*(e*f+d*g)) \\[Star] Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p,0] && LtQ[n,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let n_plus_one = &n_ + Atom::num(1);
            let direct = -e__.pow(2)
                * first_affine.pow(&m_ - Atom::num(1))
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&n_plus_one * (&c__ * &e__ * &f__ + &c__ * &d__ * &g__));
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * second_affine.pow(&n_ + Atom::num(1))
                    * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &e__ * (&m_ - &n_ - Atom::num(2))
                / (&n_plus_one * (&e__ * &f__ + &d__ * &g__));
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 704,
        source: "Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
          2*e^2 \\[Star] Subst[Int[1/(c*(e*f+d*g)+e^2*g*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt()
            / ((f__ + g__ * x_) * (a__ + c__ * x_.pow(2)).sqrt()),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&c__ * (&e__ * &f__ + &d__ * &g__)
                        + e__.pow(2) * &g__ * sub.pow(2))),
                sub_symbol,
            );
            let substituted = rubi_subst(
                &primitive,
                sub_symbol,
                (&a__ + &c__ * x_.pow(2)).sqrt()
                    / (&d__ + &e__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) * e__.pow(2), substituted)
        },
    ));
}

fn push_rules_rule_705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 705,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p-1,0] && EqQ[e*f*(p+1)-d*g*(2*n+p+3),0] && NeQ[n+p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && eqq!(
                    &e__ * &f__ * (&p_ + Atom::num(1))
                        - &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3)),
                    0
                )
                && neq!(&n_ + &p_ + Atom::num(2), 0)
        },
        rhs: {
            rubi_simp(&(e__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(2))
                    * (&f__ + &g__ * x_).pow(&n_ + Atom::num(1))
                    * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / (&c__ * &g__ * (&n_ + &p_ + Atom::num(2)))), x_)
        },
    ));
}

fn push_rules_rule_706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 706,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+1)*(e*f+d*g)) -
          e*(e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+1)*(e*f+d*g)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p-1,0] && LtQ[n,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let ef_plus_dg = &e__ * &f__ + &d__ * &g__;
            let direct = e__.pow(2)
                * (&e__ * &f__ - &d__ * &g__)
                * first_affine.pow(&m_ - Atom::num(2))
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * &g__ * (&n_ + Atom::num(1)) * &ef_plus_dg);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_ + Atom::num(1))
                    * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = &e__
                * (&e__ * &f__ * (&p_ + Atom::num(1))
                    - &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3)))
                / (&g__ * (&n_ + Atom::num(1)) * &ef_plus_dg);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 707,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) -
          (e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+p+2)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+p-1,0] && Not[LtQ[n,-1]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && !ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let balance = &n_ + &p_ + Atom::num(2);
            let direct = e__.pow(2)
                * first_affine.pow(&m_ - Atom::num(2))
                * second_affine.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * &g__ * &balance);
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * second_affine.pow(&n_)
                    * quadratic.pow(&p_)),
                x_,
            );
            let coefficient = (&e__ * &f__ * (&p_ + Atom::num(1))
                - &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3)))
                / (&g__ * &balance);
            rubi_simp(&(direct), x_) - rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 708,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[a+c*x^2],(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,c,d,e,f,g,n,p},x] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p-1/2] && ILtQ[m,0] && ILtQ[n,0] && Not[IGtQ[n,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && integerq!(&p_ - Atom::num(1) / 2)
                && iltq!(m_, 0)
                && iltq!(n_, 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let first = Atom::num(1) / (&a__ + &c__ * x_.pow(2)).sqrt();
            let second = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1) / 2);
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 709,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
        FreeQ[{a,c,d,e,f,g,n,p},x] && EqQ[c*d^2+a*e^2,0] && ILtQ[m,0] && (ILtQ[n,0] || IGtQ[n,0] && ILtQ[p+1/2,0]) && Not[IGtQ[n,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && (iltq!(n_, 0)
                    || igtq!(n_, 0) && iltq!(&p_ + Atom::num(1) / 2, 0))
                && !igtq!(n_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 710,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+c*x^2)^p,(d+e*x)^m*(f+g*x)^n,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+n+2*p+1,0] && ILtQ[m,0] && ILtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && iltq!(m_, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let first = (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let second = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_);
            let expanded = rubi_expand_integrand_product(&first, &second, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 711,
        source: "Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(a_.+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^p*
            ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-2*e*g^n*(m+p+n)*(d+e*x)^(n-2)*(a*e-c*d*x),x],x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && IGtQ[n,0] && NeQ[m+n+2*p+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, c__, d__, e__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(n_, 0)
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
                    - Atom::num(2)
                        * &e__
                        * g__.pow(&n_)
                        * (&m_ + &p_ + &n_)
                        * first_affine.pow(&n_ - Atom::num(2))
                        * (&a__ * &e__ - &c__ * &d__ * x_)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 712,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a+c*x^2,x],
                R=Coeff[PolynomialRemainder[(f+g*x)^n,a+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(f+g*x)^n,a+c*x^2,x],x,1]},
          (d+e*x)^m*(a+c*x^2)^(p+1)*(a*S-c*R*x)/(2*a*c*(p+1)) +
          1/(2*a*c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*
            ExpandToSum[2*a*c*(p+1)*(d+e*x)*Q-a*e*S*m+c*d*R*(2*p+3)+c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && GtQ[m,0] && NeQ[c*d^2+a*e^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let second_power = (&f__ + &g__ * x_).pow(&n_);
            let capital_q = rubi_polynomial_quotient(&second_power, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&second_power, &quadratic, x_).rubi_rhs();
            let capital_r = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let capital_s = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let denominator = Atom::num(2) * &a__ * &c__ * (&p_ + Atom::num(1));
            let direct = first_affine.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * (&a__ * &capital_s - &c__ * &capital_r * x_)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(Atom::num(2)
                    * &a__
                    * &c__
                    * (&p_ + Atom::num(1))
                    * &first_affine
                    * capital_q
                    - &a__ * &e__ * &capital_s * &m_
                    + &c__ * &d__ * &capital_r * (Atom::num(2) * &p_ + Atom::num(3))
                    + &c__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 713,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(d+e*x)^m*(f+g*x)^n,a+c*x^2,x],
                R=Coeff[PolynomialRemainder[(d+e*x)^m*(f+g*x)^n,a+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(d+e*x)^m*(f+g*x)^n,a+c*x^2,x],x,1]},
          (a*S-c*R*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) +
          1/(2*a*c*(p+1)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
            ExpandToSum[2*a*c*(p+1)*(d+e*x)^(-m)*Q+c*R*(2*p+3)*(d+e*x)^(-m),x],x]] /;
        FreeQ[{a,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && ILtQ[m,0] && NeQ[c*d^2+a*e^2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * &a__ * &c__ * &raised_p;

            let first_denominator = first_affine.pow(-m_i);
            let (capital_q, capital_r) = polynomial_quotient_remainder_rational_dividend(
                &second_affine.pow(n_i),
                &first_denominator,
                &quadratic,
                x_,
            ).rubi_rhs();
            let capital_r_constant = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let capital_r_linear = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct = (&a__ * &capital_r_linear - &c__ * &capital_r_constant * x_)
                * quadratic.pow(&raised_p)
                / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&denominator * &first_denominator * capital_q
                    + &c__
                        * &capital_r_constant
                        * (Atom::num(2) * &p_ + Atom::num(3))
                        * &first_denominator),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * quadratic.pow(raised_p)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 714,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a+c*x^2,x],
                R=Coeff[PolynomialRemainder[(f+g*x)^n,a+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(f+g*x)^n,a+c*x^2,x],x,1]},
          -(d+e*x)^(m+1)*(a+c*x^2)^(p+1)*(a*(e*R-d*S)+(c*d*R+a*e*S)*x)/(2*a*(p+1)*(c*d^2+a*e^2)) +
          1/(2*a*(p+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
           ExpandToSum[2*a*(p+1)*(c*d^2+a*e^2)*Q+c*d^2*R*(2*p+3)-a*e*(d*S*m-e*R*(m+2*p+3))+e*(c*d*R+a*e*S)*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,c,d,e,f,g,m},x] && IGtQ[n,1] && LtQ[p,-1] && NeQ[c*d^2+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_power = (&f__ + &g__ * x_).pow(&n_);
            let quadratic = &a__ + &c__ * x_.pow(2);
            let capital_q = rubi_polynomial_quotient(&second_power, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&second_power, &quadratic, x_).rubi_rhs();
            let capital_r = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let capital_s = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator =
                Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &invariant;
            let direct = -first_affine.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                * (&a__ * (&e__ * &capital_r - &d__ * &capital_s)
                    + (&c__ * &d__ * &capital_r + &a__ * &e__ * &capital_s) * x_)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(Atom::num(2)
                    * &a__
                    * (&p_ + Atom::num(1))
                    * &invariant
                    * capital_q
                    + &c__ * d__.pow(2) * &capital_r * (Atom::num(2) * &p_ + Atom::num(3))
                    - &a__
                        * &e__
                        * (&d__ * &capital_s * &m_
                            - &e__ * &capital_r * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                    + &e__
                        * (&c__ * &d__ * &capital_r + &a__ * &e__ * &capital_s)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * quadratic.pow(&p_ + Atom::num(1))
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_715(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 715,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,d+e*x,x], R=PolynomialRemainder[(f+g*x)^n,d+e*x,x]},
          (e*R*(d+e*x)^(m+1)*(a+c*x^2)^(p+1))/((m+1)*(c*d^2+a*e^2)) +
          1/((m+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p*
             ExpandToSum[(m+1)*(c*d^2+a*e^2)*Q+c*d*R*(m+1)-c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,c,d,e,f,g,p},x] && IGtQ[n,1] && ILtQ[m,-1] && NeQ[c*d^2+a*e^2,0] && (NeQ[m+n,0] || EqQ[p,-1/2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, p_], x_)
                && igtq!(n_, 1)
                && iltq!(m_, -1)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && (neq!(&m_ + &n_, 0) || eqq!(p_, Atom::num(-1) / 2))
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
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_716(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 716,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+c*x^2)^p*ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-
            g^n*(d+e*x)^(n-2)*(a*e^2*(m+n-1)-c*d^2*(m+n+2*p+1)-2*c*d*e*(m+n+p)*x),x],x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && IGtQ[n,1] && IntegerQ[m] && NeQ[m+n+2*p+1,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_)
                && igtq!(n_, 1)
                && integerq!(m_)
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
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 717,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n},x] && EqQ[c*d^2+a*e^2,0] && GtQ[a,0] && GtQ[d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && gtq!(a__, 0)
                && gtq!(d__, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_ + &p_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ / &d__ + &c__ / &e__ * x_).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 718,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
          (a+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p]) \\[Star] Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,n},x] && EqQ[c*d^2+a*e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [c__, e__, f__, g__, m_, n_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, n_], x_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let transformed_affine = &a__ / &d__ + &c__ / &e__ * x_;
            let frac_p = rubi_frac_part(&p_);
            let coefficient = quadratic.pow(&frac_p)
                / (first_affine.pow(&frac_p) * transformed_affine.pow(&frac_p));
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + &p_)
                    * (&f__ + &g__ * x_).pow(&n_)
                    * transformed_affine.pow(&p_)),
                x_,
            );
            rubi_star(coefficient, primitive)
        },
    ));
}

fn push_rules_rule_719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 719,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
          g/e \\[Star] Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] + (e*f-d*g)/e \\[Star] Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
        FreeQ[{a,c,d,e,f,g,m,p},x] && Not[IGtQ[m,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [c__, d__, e__, f__, g__, p_],
        x_free: [a__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_, p_], x_) && !igtq!(m_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let quadratic_power = (&a__ + &c__ * x_.pow(2)).pow(&p_);
            let first_primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * &quadratic_power),
                x_,
            );
            let second_primitive =
                rubi_rhs_int(&(first_affine.pow(&m_) * quadratic_power), x_);
            rubi_star(&g__ / &e__, first_primitive)
                    + rubi_star((&e__ * &f__ - &d__ * &g__) / &e__, second_primitive)
        },
    ));
}

fn push_rules_rule_720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 720,
        source: "Int[(a_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
          (c*d^2+a*e^2)/(e*(e*f-d*g)) \\[Star] Int[(a+c*x^2)^(p-1)/(d+e*x),x] -
          1/(e*(e*f-d*g)) \\[Star] Int[Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]*(a+c*x^2)^(p-1)/(f+g*x),x] /;
        FreeQ[{a,c,d,e,f,g},x] && FractionQ[p] && GtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern: (a__ + c__ * x_.pow(2)).pow(p_)
            / ((d__ + e__ * x_) * (f__ + g__ * x_)),
        with: [a__, c__, d__, e__, f__, g__, p_, x_],
        optional: [c__, d__, e__, f__, g__],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && fractionq!(p_)
                && gtq!(p_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic_power = (&a__ + &c__ * x_.pow(2)).pow(&p_ - Atom::num(1));
            let determinant = &e__ * &f__ - &d__ * &g__;
            let first_primitive = rubi_rhs_int(&(&quadratic_power / &first_affine), x_);
            let payload = rubi_simp(
                &(&c__ * &d__ * &f__ + &a__ * &e__ * &g__
                    - &c__ * &determinant * x_),
                x_,
            );
            let second_primitive =
                rubi_rhs_int(&(payload * quadratic_power / second_affine), x_);
            rubi_star((&c__ * d__.pow(2) + &a__ * e__.pow(2))
                        / (&e__ * &determinant), first_primitive) - rubi_star(Atom::num(1) / (&e__ * determinant), second_primitive)
        },
    ));
}

fn push_rules_rule_721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 721,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(e*(m+1)) -
          1/(2*e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*Simp[a*g+2*c*f*x+3*c*g*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_root = (&f__ + &g__ * x_).sqrt();
            let quadratic_root = (&a__ + &c__ * x_.pow(2)).sqrt();
            let denominator = &e__ * (&m_ + Atom::num(1));
            let direct = first_affine.pow(&m_ + Atom::num(1))
                * &second_root
                * &quadratic_root
                / &denominator;
            let payload = rubi_simp(
                &(&a__ * &g__
                    + Atom::num(2) * &c__ * &f__ * x_
                    + Atom::num(3) * &c__ * &g__ * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ + Atom::num(1)) * payload
                    / (second_root * quadratic_root)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), primitive)
        },
    ));
}

fn push_rules_rule_722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 722,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2],x_Symbol] :=
          2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(e*(2*m+5)) +
          1/(e*(2*m+5)) \\[Star] Int[(d+e*x)^m/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[3*a*e*f-a*d*g-2*(c*d*f-a*e*g)*x+(c*e*f-3*c*d*g)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g,m},x] && IntegerQ[2*m] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_)
                && integerq!(Atom::num(2) * &m_)
                && !ltq!(m_, -1)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_root = (&f__ + &g__ * x_).sqrt();
            let quadratic_root = (&a__ + &c__ * x_.pow(2)).sqrt();
            let denominator = &e__ * (Atom::num(2) * &m_ + Atom::num(5));
            let direct = Atom::num(2)
                * first_affine.pow(&m_ + Atom::num(1))
                * &second_root
                * &quadratic_root
                / &denominator;
            let payload = rubi_simp(
                &(Atom::num(3) * &a__ * &e__ * &f__
                    - &a__ * &d__ * &g__
                    - Atom::num(2)
                        * (&c__ * &d__ * &f__ - &a__ * &e__ * &g__)
                        * x_
                    + (&c__ * &e__ * &f__ - Atom::num(3) * &c__ * &d__ * &g__)
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_) * payload / (second_root * quadratic_root)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 723,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[a_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
          2*(d+e*x)^m*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(g*(2*m+3)) -
          1/(g*(2*m+3)) \\[Star] Int[(d+e*x)^(m-1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
            Simp[2*a*(e*f*m-d*g*(m+1))+(2*c*d*f-2*a*e*g)*x-(2*c*(d*g*m-e*f*(m+1)))*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,g},x] && IntegerQ[2*m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (a__ + c__ * x_.pow(2)).sqrt()
            / (f__ + g__ * x_).sqrt(),
        with: [a__, c__, d__, e__, f__, g__, m_, x_],
        optional: [c__, d__, e__, f__, g__, m_],
        x_free: [a__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_root = (&f__ + &g__ * x_).sqrt();
            let quadratic_root = (&a__ + &c__ * x_.pow(2)).sqrt();
            let denominator = &g__ * (Atom::num(2) * &m_ + Atom::num(3));
            let direct = Atom::num(2)
                * first_affine.pow(&m_)
                * &second_root
                * &quadratic_root
                / &denominator;
            let payload = rubi_simp(
                &(Atom::num(2)
                    * &a__
                    * (&e__ * &f__ * &m_ - &d__ * &g__ * (&m_ + Atom::num(1)))
                    + (Atom::num(2) * &c__ * &d__ * &f__
                        - Atom::num(2) * &a__ * &e__ * &g__)
                        * x_
                    - Atom::num(2)
                        * &c__
                        * (&d__ * &g__ * &m_ - &e__ * &f__ * (&m_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_affine.pow(&m_ - Atom::num(1)) * payload
                    / (second_root * quadratic_root)),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn section_contains_each_ported_downvalue_order_once() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let mut orders = rules
            .iter()
            .map(|rule| {
                rule.downvalue_order
                    .expect("section rule must have an order")
            })
            .collect::<Vec<_>>();
        orders.sort_unstable();

        let expected = std::iter::once(555).chain(639..=723).collect::<Vec<_>>();
        assert_eq!(orders, expected);
    }
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
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (e__ + f__ * x_).pow(n_) * (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (e__ + f__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (f__ + g__ * x_) * (a__ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_) * (a__ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
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
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_) / (a__ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).sqrt() * (a__ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_) / (a__ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
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
