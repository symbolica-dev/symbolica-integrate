use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5240(rules);
    push_rules_rule_5241(rules);
    push_rules_rule_5242(rules);
    push_rules_rule_5243(rules);
    push_rules_rule_5244(rules);
    push_rules_rule_5245(rules);
    push_rules_rule_5246(rules);
    push_rules_rule_5247(rules);
    push_rules_rule_5248(rules);
    push_rules_rule_5249(rules);
    // Block 6 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_5250(rules);
    push_rules_rule_5251(rules);
    push_rules_rule_5252(rules);
    push_rules_rule_5253(rules);
    push_rules_rule_5254(rules);
    push_rules_rule_5255(rules);
    push_rules_rule_5256(rules);
    push_rules_rule_5257(rules);
    push_rules_rule_5258(rules);
    push_rules_rule_5259(rules);
    push_rules_rule_5260(rules);
    push_rules_rule_5261(rules);
    push_rules_rule_5262(rules);
    push_rules_rule_5263(rules);
    push_rules_rule_5264(rules);
    push_rules_rule_5265(rules);
    push_rules_rule_5266(rules);
    push_rules_rule_5267(rules);
    push_rules_rule_5268(rules);
    push_rules_rule_5269(rules);
    push_rules_rule_5270(rules);
    push_rules_rule_5271(rules);
    push_rules_rule_5272(rules);
    push_rules_rule_5273(rules);
    push_rules_rule_5274(rules);
    push_rules_rule_5275(rules);
    push_rules_rule_5276(rules);
    push_rules_rule_5277(rules);
    push_rules_rule_5278(rules);
    push_rules_rule_5279(rules);
    push_rules_rule_5280(rules);
    push_rules_rule_5281(rules);
    push_rules_rule_5282(rules);
    push_rules_rule_5283(rules);
    push_rules_rule_5284(rules);
    push_rules_rule_5285(rules);
    push_rules_rule_5286(rules);
    push_rules_rule_5287(rules);
    push_rules_rule_5288(rules);
    push_rules_rule_5289(rules);
    push_rules_rule_5290(rules);
    push_rules_rule_5291(rules);
    push_rules_rule_5292(rules);
    push_rules_rule_5293(rules);
    push_rules_rule_5294(rules);
    push_rules_rule_5295(rules);
    push_rules_rule_5296(rules);
    push_rules_rule_5297(rules);
    push_rules_rule_5298(rules);
    push_rules_rule_5299(rules);
    push_rules_rule_5300(rules);
    push_rules_rule_5301(rules);
}

fn push_rules_rule_5240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5240,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
          Subst[Int[(a+b*x)^n*Cos[x]/(c*d+e*Sin[x]),x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&a__ + &b__ * &sub_atom).pow(&n_) * &sub_atom.cos() / (&c__ * &d__ + &e__ * sub_atom.sin());
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                (&c__ * x_).asin(),
            )
        },
    ));
}

fn push_rules_rule_5241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5241,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_),x_Symbol] :=
          -Subst[Int[(a+b*x)^n*Sin[x]/(c*d+e*Cos[x]),x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&a__ + &b__ * &sub_atom).pow(&n_) * &sub_atom.sin() / (&c__ * &d__ + &e__ * sub_atom.cos());
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            -rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                (&c__ * x_).acos(),
            )
        },
    ));
}

fn push_rules_rule_5242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5242,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcSin[c*x])^n/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let direct =
                linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&e__ * (&m_ + Atom::num(1)));
            let coefficient = -&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1)));

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive_primitive)
        },
    ));
}

fn push_rules_rule_5243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5243,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCos[c*x])^n/(e*(m+1)) +
          b*c*n/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let direct =
                linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&e__ * (&m_ + Atom::num(1)));
            let coefficient = &b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1)));

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive_primitive)
        },
    ));
}

fn push_rules_rule_5244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5244,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(m_, 0) && ltq!(n_, -1) },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5245,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && igtq!(m_, 0) && ltq!(n_, -1) },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5246,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Cos[x]*(c*d+e*Sin[x])^m,x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_)
                * &sub_atom.cos()
                * (&c__ * &d__ + &e__ * sub_atom.sin()).pow(&m_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / c__.pow(&m_ + Atom::num(1)), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    (&c__ * x_).asin(),
                ))
        },
    ));
}

fn push_rules_rule_5247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5247,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Sin[x]*(c*d+e*Cos[x])^m,x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_)
                * &sub_atom.sin()
                * (&c__ * &d__ + &e__ * sub_atom.cos()).pow(&m_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(-Atom::num(1) / c__.pow(&m_ + Atom::num(1)), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    (&c__ * x_).acos(),
                ))
        },
    ));
}

fn push_rules_rule_5248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, px__, x_);
    rules.push(rubi_rule!(
        order: 5248,
        source: "Int[Px_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[ExpandExpression[Px,x],x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).asin()),
        with: [px__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let expanded_px = rubi_expand_expression(&px__, x_);
            let u = rubi_int_hide(&expanded_px, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, px__, x_);
    rules.push(rubi_rule!(
        order: 5249,
        source: "Int[Px_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[ExpandExpression[Px,x],x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).acos()),
        with: [px__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let expanded_px = rubi_expand_expression(&px__, x_);
            let u = rubi_int_hide(&expanded_px, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 5250,
        source: "Int[Px_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [px__, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let integrand = &px__ * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 5251,
        source: "Int[Px_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c,n},x] && PolynomialQ[Px,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [px__, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && rubi_polynomial_q(&px__, x_) },
        rhs: {
            let integrand = &px__ * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, px__, x_);
    rules.push(rubi_rule!(
        order: 5252,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[Px*(d+e*x)^m,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()),
        with: [px__, d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && rubi_polynomial_q(&px__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&(&px__ * (&d__ + &e__ * x_).pow(&m_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, px__, x_);
    rules.push(rubi_rule!(
        order: 5253,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[Px*(d+e*x)^m,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && PolynomialQ[Px,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()),
        with: [px__, d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_) && rubi_polynomial_q(&px__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&(&px__ * (&d__ + &e__ * x_).pow(&m_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5254,
        source: "Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},
          (a+b*ArcSin[c*x])^n \\[Star] u - b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(p_) * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [f__, g__, p_, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [f__, g__, p_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(m_, 0)
                && ltq!(&m_ + &p_ + Atom::num(1), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&p_) * (&d__ + &e__ * x_).pow(&m_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5255,
        source: "Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},
          (a+b*ArcCos[c*x])^n \\[Star] u + b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(p_) * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [f__, g__, p_, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [f__, g__, p_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(m_, 0)
                && ltq!(&m_ + &p_ + Atom::num(1), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&p_) * (&d__ + &e__ * x_).pow(&m_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    + rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5256,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
          With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},
          (a+b*ArcSin[c*x])^n \\[Star] u - b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
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
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_ + &h__ * x_.pow(2)).pow(&p_)
                    / (&d__ + &e__ * x_).pow(2)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5257,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
          With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},
          (a+b*ArcCos[c*x])^n \\[Star] u + b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
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
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_ + &h__ * x_.pow(2)).pow(&p_)
                    / (&d__ + &e__ * x_).pow(2)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    + rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 5258,
        source: "Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [px__, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&px__, x_)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 5259,
        source: "Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [px__, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&px__, x_)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5260,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[1/Sqrt[1-c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [g__, m_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && iltq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && (ltq!(m_, (Atom::num(-2) * &p_ - Atom::num(1))) || gtq!(m_, 3))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_5261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5261,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f+g*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[1/Sqrt[1-c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d,0] && (LtQ[m,-2*p-1] || GtQ[m,3])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [g__, m_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && iltq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && (ltq!(m_, (Atom::num(-2) * &p_ - Atom::num(1))) || gtq!(m_, 3))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    + rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_5262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5262,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] &&
          (m==1 || p>0 || n==1 && p>-1 || m==2 && p<-2)",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && integerq!(&p_ + half_integer_atom(1))
                && gtq!(d__, 0)
                && igtq!(n_, 0)
                && (eqq!(m_, 1)
                    || gtq!(p_, 0)
                    || (eqq!(n_, 1) && gtq!(p_, -1))
                    || (eqq!(m_, 2) && ltq!(p_, -2)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * argument.pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5263,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d,0] && IGtQ[n,0] &&
          (m==1 || p>0 || n==1 && p>-1 || m==2 && p<-2)",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && integerq!(&p_ + half_integer_atom(1))
                && gtq!(d__, 0)
                && igtq!(n_, 0)
                && (eqq!(m_, 1)
                    || gtq!(p_, 0)
                    || (eqq!(n_, 1) && gtq!(p_, -1))
                    || (eqq!(m_, 2) && ltq!(p_, -2)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * argument.pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5264,
        source: "Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d+e*x^2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          1/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [f__, g__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [g__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && iltq!(m_, 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = (&d__ * &g__ * &m_
                + Atom::num(2) * &e__ * &f__ * x_
                + &e__ * &g__ * (&m_ + Atom::num(2)) * x_.pow(2))
                * linear.pow(&m_ - Atom::num(1))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(linear.pow(&m_) * quadratic * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5265,
        source: "Int[(f_+g_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -(f+g*x)^m*(d+e*x^2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) +
          1/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(d*g*m+2*e*f*x+e*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [f__, g__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [g__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && iltq!(m_, 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = (&d__ * &g__ * &m_
                + Atom::num(2) * &e__ * &f__ * x_
                + &e__ * &g__ * (&m_ + Atom::num(2)) * x_.pow(2))
                * linear.pow(&m_ - Atom::num(1))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(-linear.pow(&m_) * quadratic * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5266,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let u = &quadratic.sqrt() * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic.pow(&p_ - half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5267,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n,(f+g*x)^m*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let u = &quadratic.sqrt() * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic.pow(&p_ - half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5268,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          1/(b*c*Sqrt[d]*(n+1)) \\[Star]
            Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && iltq!(m_, 0)
                && igtq!(&p_ - half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let multiplier = &d__ * &g__ * &m_
                + &e__ * &f__ * (Atom::num(2) * &p_ + Atom::num(1)) * x_
                + &e__ * &g__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1)) * x_.pow(2);
            let u = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let v = multiplier * quadratic.pow(&p_ - half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_simp(&(linear.pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1)) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_5269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5269,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -(f+g*x)^m*(d+e*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) +
          1/(b*c*Sqrt[d]*(n+1)) \\[Star]
            Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),(d*g*m+e*f*(2*p+1)*x+e*g*(m+2*p+1)*x^2)*(d+e*x^2)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && iltq!(m_, 0)
                && igtq!(&p_ - half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let multiplier = &d__ * &g__ * &m_
                + &e__ * &f__ * (Atom::num(2) * &p_ + Atom::num(1)) * x_
                + &e__ * &g__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1)) * x_.pow(2);
            let u = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let v = multiplier * quadratic.pow(&p_ - half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_simp(&(-linear.pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1)) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_5270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5270,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f+g*x)^m*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(f+g*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && gtq!(d__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5271,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -(f+g*x)^m*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) +
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(f+g*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IGtQ[m,0] && GtQ[d,0] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(m_, 0)
                && gtq!(d__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(-linear.pow(&m_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5272,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/(c^(m+1)*Sqrt[d]) \\[Star] Subst[Int[(a+b*x)^n*(c*f+g*Sin[x])^m,x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && gtq!(d__, 0)
                && (gtq!(m_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * (&c__ * &f__ + &g__ * sub_atom.sin()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / (c__.pow(&m_ + Atom::num(1)) * d__.sqrt()), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asin()))
        },
    ));
}

fn push_rules_rule_5273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5273,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -1/(c^(m+1)*Sqrt[d]) \\[Star] Subst[Int[(a+b*x)^n*(c*f+g*Cos[x])^m,x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && GtQ[d,0] && (GtQ[m,0] || IGtQ[n,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [g__, m_, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && gtq!(d__, 0)
                && (gtq!(m_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * (&c__ * &f__ + &g__ * sub_atom.cos()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-Atom::num(1) / (c__.pow(&m_ + Atom::num(1)) * d__.sqrt()), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acos()))
        },
    ));
}

fn push_rules_rule_5274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5274,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && iltq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let u = (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_) / &quadratic.sqrt();
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5275,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f+g*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && iltq!(&p_ + half_integer_atom(1), 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let u = (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_) / &quadratic.sqrt();
            let v = (&f__ + &g__ * x_).pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5276,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && integerq!(&p_ - half_integer_atom(1))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = (&f__ + &g__ * x_).pow(&m_) * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5277,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f+g*x)^m*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && integerq!(&p_ - half_integer_atom(1))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = (&f__ + &g__ * x_).pow(&m_) * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5278,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          Log[h*(f+g*x)^m]*(a+b*ArcSin[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) -
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(a+b*ArcSin[c*x])^(n+1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [h__, f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [h__, f__, g__, m_, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let log_part = (&h__ * linear.pow(&m_)).log();
            let recursive = argument.pow(&n_ + Atom::num(1)) / linear;
            rubi_simp(&(log_part * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5279,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -Log[h*(f+g*x)^m]*(a+b*ArcCos[c*x])^(n+1)/(b*c*Sqrt[d]*(n+1)) +
          g*m/(b*c*Sqrt[d]*(n+1)) \\[Star] Int[(a+b*ArcCos[c*x])^(n+1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && EqQ[c^2*d+e,0] && GtQ[d,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [h__, f__, g__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [h__, f__, g__, m_, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let log_part = (&h__ * linear.pow(&m_)).log();
            let recursive = argument.pow(&n_ + Atom::num(1)) / linear;
            rubi_simp(&(-log_part * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&g__ * &m_ / (&b__ * &c__ * d__.sqrt() * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5280,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [h__, f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [h__, f__, g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = (&h__ * (&f__ + &g__ * x_).pow(&m_)).log() * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5281,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[Log[h*(f+g*x)^m]*(1-c^2*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && Not[GtQ[d,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log() * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [h__, f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [h__, f__, g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && !gtq!(d__, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = (&h__ * (&f__ + &g__ * x_).pow(&m_)).log() * unit.pow(&p_) * argument.pow(&n_);
            rubi_star(rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5282,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[1/Sqrt[1-c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, x_],
        optional: [e__, g__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_) && iltq!(&m_ + half_integer_atom(1), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&((&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_)), x_).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_5283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5283,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[1/Sqrt[1-c^2*x^2] \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, x_],
        optional: [e__, g__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_) && iltq!(&m_ + half_integer_atom(1), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&((&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_)), x_).rubi_rhs();
            let reciprocal = Atom::num(1) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_star(argument, &u)
                    + rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_5284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5284,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, n_, x_],
        optional: [e__, m_, g__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) && integerq!(m_) },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let v = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5285,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^m*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, n_, x_],
        optional: [e__, m_, g__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) && integerq!(m_) },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let v = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 5286,
        source: "Int[u_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcSin[c*x]) \\[Star] v - b*c \\[Star] Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asin()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&v / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, v) - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 5287,
        source: "Int[u_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcCos[c*x]) \\[Star] v + b*c \\[Star] Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acos()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&v / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, v) + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 5288,
        source: "Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [px__, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && {
                    let integrand =
                        &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 5289,
        source: "Int[Px_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [px__, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && {
                    let integrand =
                        &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand =
                &px__ * (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 5290,
        source: "Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcSin[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (f__ + g__ * (d__ + e__ * x_.pow(2)).pow(p_)).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [px__, f__, g__, d__, e__, p_, m_, a__, b__, c__, n_, x_],
        optional: [px__, g__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && integersq!([m_, n_])
                && {
                    let integrand = &px__
                        * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                        * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand = &px__
                * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 5291,
        source: "Int[Px_.*(f_+g_.*(d_+e_.*x_^2)^p_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(f+g*(d+e*x^2)^p)^m*(a+b*ArcCos[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && PolynomialQ[Px,x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (f__ + g__ * (d__ + e__ * x_.pow(2)).pow(p_)).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [px__, f__, g__, d__, e__, p_, m_, a__, b__, c__, n_, x_],
        optional: [px__, g__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && rubi_polynomial_q(&px__, x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && integersq!([m_, n_])
                && {
                    let integrand = &px__
                        * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                        * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand = &px__
                * (&f__ + &g__ * (&d__ + &e__ * x_.pow(2)).pow(&p_)).pow(&m_)
                * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5292,
        source: "Int[RFx_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[ArcSin[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (c__ * x_).asin().pow(n_),
        with: [rfx__, c__, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!(c__, x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && {
                    let u = (&c__ * x_).asin().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&c__ * x_).asin().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5293,
        source: "Int[RFx_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[ArcCos[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (c__ * x_).acos().pow(n_),
        with: [rfx__, c__, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!(c__, x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && {
                    let u = (&c__ * x_).acos().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&c__ * x_).acos().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5294,
        source: "Int[RFx_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[RFx*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (Atom::var(a_) + b__ * (c__ * x_).asin()).pow(n_),
        with: [rfx__, a_, b__, c__, n_, x_],
        optional: [b__, c__, n_],
        when: { freeq!([a_, b__, c__], x_) && rubi_rational_function_q(&rfx__, x_) && igtq!(n_, 0) },
        rhs: {
            let integrand = &rfx__ * (&a_ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5295,
        source: "Int[RFx_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[RFx*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (Atom::var(a_) + b__ * (c__ * x_).acos()).pow(n_),
        with: [rfx__, a_, b__, c__, n_, x_],
        optional: [b__, c__, n_],
        when: { freeq!([a_, b__, c__], x_) && rubi_rational_function_q(&rfx__, x_) && igtq!(n_, 0) },
        rhs: {
            let integrand = &rfx__ * (&a_ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5296,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*ArcSin[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcSin[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (c__ * x_).asin().pow(n_),
        with: [rfx__, d__, e__, p_, c__, n_, x_],
        optional: [e__, c__, n_],
        when: {
            freeq!([c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && {
                    let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).asin().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).asin().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5297,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*ArcCos[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(d+e*x^2)^p*ArcCos[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (c__ * x_).acos().pow(n_),
        with: [rfx__, d__, e__, p_, c__, n_, x_],
        optional: [e__, c__, n_],
        when: {
            freeq!([c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && {
                    let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).acos().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&c__ * x_).acos().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5298,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcSin[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (Atom::var(a_) + b__ * (c__ * x_).asin()).pow(n_),
        with: [rfx__, d__, e__, p_, a_, b__, c__, n_, x_],
        optional: [e__, b__, c__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let v = &rfx__ * (&a_ + &b__ * (&c__ * x_).asin()).pow(&n_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 5299,
        source: "Int[RFx_*(d_+e_.*x_^2)^p_*(a_+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^p,RFx*(a+b*ArcCos[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d__ + e__ * x_.pow(2)).pow(p_) * (Atom::var(a_) + b__ * (c__ * x_).acos()).pow(n_),
        with: [rfx__, d__, e__, p_, a_, b__, c__, n_, x_],
        optional: [e__, b__, c__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let v = &rfx__ * (&a_ + &b__ * (&c__ * x_).acos()).pow(&n_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 5300,
        source: "Int[u_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: Atom::var(u_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [u_, a__, b__, c__, n_, x_],
        optional: [u_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let integrand = u_ * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 5301,
        source: "Int[u_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: Atom::var(u_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [u_, a__, b__, c__, n_, x_],
        optional: [u_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let integrand = u_ * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5240_through_5242_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5240..=5242).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5240..=5242).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5193_through_5242_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5193..=5242).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5193..=5242).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5243_through_5292_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5243..=5292).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5243..=5292).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5243_through_5292_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5243..=5292).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5243..=5292).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5293_through_5301_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5293..=5301).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5293..=5301).collect::<Vec<_>>());
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
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
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
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
        / (d__ + e__ * x_.pow(2)).sqrt()
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
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
        / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
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
        * (a__ + b__ * (c__ * x_).acos()).pow(n_)
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
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(2)).pow(p_)
        * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}
