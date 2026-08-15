use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6242(rules);
    push_rules_rule_6243(rules);
    push_rules_rule_6244(rules);
    push_rules_rule_6245(rules);
    push_rules_rule_6246(rules);
    // Block 6 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6247(rules);
    push_rules_rule_6248(rules);
    push_rules_rule_6249(rules);
    push_rules_rule_6250(rules);
    push_rules_rule_6251(rules);
    push_rules_rule_6252(rules);
    push_rules_rule_6253(rules);
    push_rules_rule_6254(rules);
    push_rules_rule_6255(rules);
    push_rules_rule_6256(rules);
    push_rules_rule_6257(rules);
    push_rules_rule_6258(rules);
    push_rules_rule_6259(rules);
    push_rules_rule_6260(rules);
    push_rules_rule_6261(rules);
    push_rules_rule_6262(rules);
    push_rules_rule_6263(rules);
    push_rules_rule_6264(rules);
    push_rules_rule_6265(rules);
    push_rules_rule_6266(rules);
    push_rules_rule_6267(rules);
    push_rules_rule_6268(rules);
    push_rules_rule_6269(rules);
    push_rules_rule_6270(rules);
    push_rules_rule_6271(rules);
    push_rules_rule_6272(rules);
}

fn push_rules_rule_6242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6242,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_.+e_.*x_),x_Symbol] :=
          Subst[Int[(a+b*x)^n*Cosh[x]/(c*d+e*Sinh[x]),x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cosh()
                / (&c__ * &d__ + &e__ * sub_atom.sinh());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asinh())
        },
    ));
}

fn push_rules_rule_6243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6243,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^n/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && igtq!(n_, 0) && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive = linear.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let direct =
                linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&e__ * (&m_ + Atom::num(1)));
            let coefficient = -&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1)));

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6244,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(m_, 0) && ltq!(n_, -1) },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6245,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Cosh[x]*(c*d+e*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_)
                * sub_atom.cosh()
                * (&c__ * &d__ + &e__ * sub_atom.sinh()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asinh());
            rubi_star(Atom::num(1) / c__.pow(&m_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_6246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, px__, x_);
    rules.push(rubi_rule!(
        order: 6246,
        source: "Int[Px_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[ExpandExpression[Px,x],x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).asinh()),
        with: [px__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let expanded_px = rubi_expand_expression(&px__, x_);
            let u = rubi_int_hide(&expanded_px, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 6247,
        source: "Int[Px_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*ArcSinh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [px__, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let integrand = &px__ * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, px__, x_);
    rules.push(rubi_rule!(
        order: 6248,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[Px*(d+e*x)^m,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()),
        with: [px__, d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && rubi_polynomial_q(&px__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(&(&px__ * (&d__ + &e__ * x_).pow(&m_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6249,
        source: "Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},
          (a+b*ArcSinh[c*x])^n \\[Star] u - b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(p_) * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [f__, g__, p_, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [f__, g__, p_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(m_, 0)
                && ltq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&p_) * (&d__ + &e__ * x_).pow(&m_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6250,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
          With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},
          (a+b*ArcSinh[c*x])^n \\[Star] u - b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
            / (d__ + e__ * x_).pow(2),
        with: [f__, g__, h__, p_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, g__, h__, p_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && eqq!(&e__ * &g__ - Atom::num(2) * &d__ * &h__, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_ + &h__ * x_.pow(2)).pow(&p_)
                    / (&d__ + &e__ * x_).pow(2)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 6251,
        source: "Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcSinh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [px__, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&px__, x_)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6252,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[1/Sqrt[1+c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [g__, m_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(m_, 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d__, 0)
                && (ltq!(m_, Atom::num(-1) * (Atom::num(2) * &p_ + 1)) || gtq!(m_, 3))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_6253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6253,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] &&
          (EqQ[n,1] && GtQ[p,-1] || GtQ[p,0] || EqQ[m,1] || EqQ[m,2] && LtQ[p,-2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(m_, 0)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
                && gtq!(d__, 0)
                && igtq!(n_, 0)
                && ((eqq!(n_, 1) && gtq!(p_, -1)) || gtq!(p_, 0) || eqq!(m_, 1) || (eqq!(m_, 2) && ltq!(p_, -2)))
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6254,
        source: "Int[(f_.+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d+e*x^2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          1/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [f__, g__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, g__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && iltq!(m_, 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive = (&d__ * &g__ * &m_ + Atom::num(2) * &e__ * &f__ * x_
                + &e__ * &g__ * (&m_ + Atom::num(2)) * x_.pow(2))
                * linear.pow(&m_ - Atom::num(1))
                * argument.pow(&n_ + Atom::num(1));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&m_) * quadratic_x * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6255,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(m_)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let u = &quadratic_x.sqrt() * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic_x.pow(&p_ - Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6256,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          1/(b*c*Sqrt[d]*(n+1)) \\[Star]
            Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && iltq!(m_, 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let multiplier = &d__ * &g__ * &m_
                + &e__ * &f__ * (Atom::num(2) * &p_ + 1) * x_
                + &e__ * &g__ * (&m_ + Atom::num(2) * &p_ + 1) * x_.pow(2);
            let u = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let v = multiplier * quadratic_x.pow(&p_ - Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            rubi_simp(&(linear.pow(&m_) * quadratic_x.pow(&p_ + Atom::num(1) / Atom::num(2))
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_6257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6257,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f+g*x)^m*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(f+g*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(m_, 0)
                && gtq!(d__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6258,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/(c^(m+1)*Sqrt[d]) \\[Star] Subst[Int[(a+b*x)^n*(c*f+g*Sinh[x])^m,x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e,c^2*d] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(m_)
                && gtq!(d__, 0)
                && (gtq!(m_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload =
                (&a__ + &b__ * &sub_atom).pow(&n_) * (&c__ * &f__ + &g__ * sub_atom.sinh()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asinh());
            rubi_star(Atom::num(1) / (c__.pow(&m_ + Atom::num(1)) * d__.sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_6259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6259,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e,c^2*d] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(m_)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let u = (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_) / &quadratic_x.sqrt();
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic_x.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6260,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f+g*x)^m*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e,c^2*d] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(m_)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive = (&f__ + &g__ * x_).pow(&m_) * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic_x.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6261,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Log[h*(f+g*x)^m]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(a+b*ArcSinh[c*x])^(n+1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[e,c^2*d] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [h__, f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [h__, f__, g__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let log_part = (&h__ * linear.pow(&m_)).log();
            let recursive = argument.pow(&n_ + Atom::num(1)) / linear;
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(log_part * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6262,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[Log[h*(f+g*x)^m]*(1+c^2*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e,c^2*d] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [h__, f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [h__, f__, g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive =
                (&h__ * (&f__ + &g__ * x_).pow(&m_)).log() * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic_x.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6263,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[1/Sqrt[1+c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, x_],
        optional: [e__, g__, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) && iltq!(&m_ + Atom::num(1) / Atom::num(2), 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(&((&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_)), x_).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_6264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6264,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(d+e*x)^m*(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, n_, x_],
        optional: [e__, m_, g__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) && integerq!(m_) },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let v = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 6265,
        source: "Int[u_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcSinh[c*x]) \\[Star] v - b*c \\[Star] Int[SimplifyIntegrand[v/Sqrt[1+c^2*x^2],x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asinh()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&v / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, v)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 6266,
        source: "Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[e,c^2*d] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [px__, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && {
                    let integrand =
                        &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 6267,
        source: "Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcSinh[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[e,c^2*d] && IGtQ[p+1/2,0] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (f__ + g__ * (d__ + e__ * x_.pow(2)).pow(p_)).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [px__, f__, g__, d__, e__, p_, m_, a__, b__, c__, n_, x_],
        optional: [px__, g__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && integersq!([m_, n_])
                && {
                    let integrand = &px__
                        * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                        * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand = &px__
                * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6268,
        source: "Int[RFx_*ArcSinh[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[ArcSinh[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (c__ * x_).asinh().pow(n_),
        with: [rfx__, c__, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!(c__, x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && {
                    let u = (&c__ * x_).asinh().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&c__ * x_).asinh().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6269,
        source: "Int[RFx_*(a_+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[RFx*(a+b*ArcSinh[c*x])^n,x],x] /;
        FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (Atom::var(a_) + b__ * (c__ * x_).asinh()).pow(n_),
        with: [rfx__, a_, b__, c__, n_, x_],
        optional: [b__, c__, n_],
        when: { freeq!([a_, b__, c__], x_) && rubi_rational_function_q(&rfx__, x_) && igtq!(n_, 0) },
        rhs: {
            let integrand = &rfx__ * (&a_ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6270,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*ArcSinh[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcSinh[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e,c^2*d] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (c__ * x_).asinh().pow(n_),
        with: [rfx__, d__, e__, p_, c__, n_, x_],
        optional: [e__, c__, n_],
        when: {
            freeq!([c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && {
                    let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).asinh().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).asinh().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6271,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcSinh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e,c^2*d] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (Atom::var(a_) + b__ * (c__ * x_).asinh()).pow(n_),
        with: [rfx__, d__, e__, p_, a_, b__, c__, n_, x_],
        optional: [e__, b__, c__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let v = &rfx__ * (&a_ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6272,
        source: "Int[u_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let integrand = u__ * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6242_through_6272_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6242..=6272).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6242..=6272).collect::<Vec<_>>());
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
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
        / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(2)).pow(p_)
        * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}
