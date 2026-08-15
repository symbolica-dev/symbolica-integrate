use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6377(rules);
    push_rules_rule_6378(rules);
    push_rules_rule_6379(rules);
    push_rules_rule_6380(rules);
    push_rules_rule_6381(rules);
    // Block 6 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6382(rules);
    push_rules_rule_6383(rules);
    push_rules_rule_6384(rules);
    push_rules_rule_6385(rules);
    push_rules_rule_6386(rules);
    push_rules_rule_6387(rules);
    push_rules_rule_6388(rules);
    push_rules_rule_6389(rules);
    push_rules_rule_6390(rules);
    push_rules_rule_6391(rules);
    push_rules_rule_6392(rules);
    push_rules_rule_6393(rules);
    push_rules_rule_6394(rules);
    push_rules_rule_6395(rules);
    push_rules_rule_6396(rules);
    push_rules_rule_6397(rules);
    push_rules_rule_6398(rules);
    push_rules_rule_6399(rules);
    push_rules_rule_6400(rules);
    push_rules_rule_6401(rules);
    push_rules_rule_6402(rules);
    push_rules_rule_6403(rules);
    push_rules_rule_6404(rules);
    push_rules_rule_6405(rules);
    push_rules_rule_6406(rules);
    push_rules_rule_6407(rules);
    push_rules_rule_6408(rules);
    push_rules_rule_6409(rules);
}

fn push_rules_rule_6377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6377,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_.+e_.*x_),x_Symbol] :=
          Subst[Int[(a+b*x)^n*Sinh[x]/(c*d+e*Cosh[x]),x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sinh()
                / (&c__ * &d__ + &e__ * sub_atom.cosh());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ * x_).acosh(),
            )
        },
    ));
}

fn push_rules_rule_6378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6378,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^n/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = linear.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1))
                / ((-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt());
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&e__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6379,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[m,0] && LtQ[n,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(m_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6380,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Sinh[x]*(c*d+e*Cosh[x])^m,x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_)
                * sub_atom.sinh()
                * (&c__ * &d__ + &e__ * sub_atom.cosh()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(Atom::num(1) / c__.pow(&m_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_6381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, px__, x_);
    rules.push(rubi_rule!(
        order: 6381,
        source: "Int[Px_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[ExpandExpression[Px,x],x]},
          (a+b*ArcCosh[c*x]) \\[Star] u -
          b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x]) \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Px,x]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).acosh()),
        with: [px__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_) && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let expanded_px = rubi_expand_expression(&px__, x_);
            let u = rubi_int_hide(&expanded_px, x_).rubi_rhs();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let denominator =
                (-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / &radical), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__ * radical / denominator, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 6382,
        source: "Int[Px_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*ArcCosh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,n},x] && PolyQ[Px,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [px__, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, n_], x_) && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let integrand = &px__ * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, px__, x_);
    rules.push(rubi_rule!(
        order: 6383,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[Px*(d+e*x)^m,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u -
          b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x]) \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Px,x]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [px__, d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&(&px__ * (&d__ + &e__ * x_).pow(&m_)), x_).rubi_rhs();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let denominator =
                (-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / &radical), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__ * radical / denominator, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6384,
        source: "Int[(f_.+g_.*x_)^p_.*(d_+e_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          With[{u=IntHide[(f+g*x)^p*(d+e*x)^m,x]},
          (a+b*ArcCosh[c*x])^n \\[Star] u -
          b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[m,0] && LtQ[m+p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(p_) * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
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
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&p_) * (&d__ + &e__ * x_).pow(&m_)),
                x_,
            ).rubi_rhs();
            let denominator =
                (-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1)) / denominator),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6385,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(d_+e_.*x_)^2,x_Symbol] :=
          With[{u=IntHide[(f+g*x+h*x^2)^p/(d+e*x)^2,x]},
          (a+b*ArcCosh[c*x])^n \\[Star] u -
          b*c*n \\[Star] Int[SimplifyIntegrand[u*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[-1+c*x]*Sqrt[1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[n,0] && IGtQ[p,0] && EqQ[e*g-2*d*h,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_).pow(2),
        with: [f__, g__, h__, p_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, g__, h__, p_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && eqq!(&e__ * &g__ - Atom::num(2) * &d__ * &h__, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_ + &h__ * x_.pow(2)).pow(&p_)
                    / (&d__ + &e__ * x_).pow(2)),
                x_,
            ).rubi_rhs();
            let denominator =
                (-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(
                &(&u * argument.pow(&n_ - Atom::num(1)) / denominator),
                x_,
            );
            rubi_star(argument.pow(&n_), u)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 6386,
        source: "Int[Px_*(d_+e_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*(a+b*ArcCosh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [px__, d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let integrand = &px__
                * (&d__ + &e__ * x_).pow(&m_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6387,
        source: "Int[(f_+g_.*x_)^m_.*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((-1+c*x)^FracPart[p]*(1+c*x)^FracPart[p]) \\[Star]
            Int[(f+g*x)^m*(-1+c*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && IntegerQ[m]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && integerq!(m_)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let frac_p_numerator = rubi_frac_part(&p_);
            let frac_p_left = rubi_frac_part(&p_);
            let frac_p_right = rubi_frac_part(&p_);
            let int_p = rubi_int_part(&p_);
            let transformed = (&f__ + &g__ * x_).pow(&m_)
                * (-Atom::num(1) + &c__ * x_).pow(&p_)
                * (Atom::num(1) + &c__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let coefficient = (-&d__).pow(int_p) * quadratic.pow(&frac_p_numerator)
                / ((-Atom::num(1) + &c__ * x_).pow(&frac_p_left)
                    * (Atom::num(1) + &c__ * x_).pow(&frac_p_right));
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_6388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6388,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (-d)^IntPart[p]*(d+e*x^2)^FracPart[p]/((-1+c*x)^FracPart[p]*(1+c*x)^FracPart[p]) \\[Star]
            Int[Log[h*(f+g*x)^m]*(-1+c*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log()
            * (d__ + e__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [h__, f__, g__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [h__, f__, g__, m_, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let frac_p_numerator = rubi_frac_part(&p_);
            let frac_p_left = rubi_frac_part(&p_);
            let frac_p_right = rubi_frac_part(&p_);
            let int_p = rubi_int_part(&p_);
            let transformed = (&h__ * (&f__ + &g__ * x_).pow(&m_)).log()
                * (-Atom::num(1) + &c__ * x_).pow(&p_)
                * (Atom::num(1) + &c__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let coefficient = (-&d__).pow(int_p) * quadratic.pow(&frac_p_numerator)
                / ((-Atom::num(1) + &c__ * x_).pow(&frac_p_left)
                    * (Atom::num(1) + &c__ * x_).pow(&frac_p_right));
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_6389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6389,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f+g*x)^m*(d1+e1*x)^p*(d2+e2*x)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[1/(Sqrt[-1+c*x]*Sqrt[1+c*x]) \\[Star] u,x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && ILtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] &&
          (GtQ[m,3] || LtQ[m,-2*p-1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && igtq!(m_, 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && (gtq!(m_, 3) || ltq!(m_, (-Atom::num(2) * &p_ - 1)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(
                &((&f__ + &g__ * x_).pow(&m_)
                    * (&d1__ + &e1__ * x_).pow(&p_)
                    * (&d2__ + &e2__ * x_).pow(&p_)),
                x_,
            ).rubi_rhs();
            let reciprocal = Atom::num(1)
                / ((-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt());
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_6390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6390,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && IntegerQ[p+1/2] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0] &&
          (EqQ[n,1] && GtQ[p,-1] || GtQ[p,0] || EqQ[m,1] || EqQ[m,2] && LtQ[p,-2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && igtq!(m_, 0)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
                && ((eqq!(n_, 1) && gtq!(p_, -1)) || gtq!(p_, 0) || eqq!(m_, 1) || (eqq!(m_, 2) && ltq!(p_, -2)))
        },
        rhs: {
            let u = (&d1__ + &e1__ * x_).pow(&p_)
                * (&d2__ + &e2__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6391,
        source: "Int[(f_+g_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d1*d2+e1*e2*x^2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) -
          1/(b*c*Sqrt[-d1*d2]*(n+1)) \\[Star] Int[(d1*d2*g*m+2*e1*e2*f*x+e1*e2*g*(m+2)*x^2)*(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && ILtQ[m,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt() * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [f__, g__, m_, d1__, e1__, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && iltq!(m_, 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let root = (-&d1__ * &d2__).sqrt();
            let recursive = (&d1__ * &d2__ * &g__ * &m_
                + Atom::num(2) * &e1__ * &e2__ * &f__ * x_
                + &e1__ * &e2__ * &g__ * (&m_ + Atom::num(2)) * x_.pow(2))
                * linear.pow(&m_ - Atom::num(1))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(linear.pow(&m_)
                    * (&d1__ * &d2__ + &e1__ * &e2__ * x_.pow(2))
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * &root * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1) / (&b__ * &c__ * root * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6392,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n,(f+g*x)^m*(d1+e1*x)^(p-1/2)*(d2+e2*x)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && IGtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(m_)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let u = (&d1__ + &e1__ * x_).sqrt()
                * (&d2__ + &e2__ * x_).sqrt()
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let v = (&f__ + &g__ * x_).pow(&m_)
                * (&d1__ + &e1__ * x_).pow(&p_ - Atom::num(1) / Atom::num(2))
                * (&d2__ + &e2__ * x_).pow(&p_ - Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6393,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f+g*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) -
          1/(b*c*Sqrt[-d1*d2]*(n+1)) \\[Star]
            Int[ExpandIntegrand[(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),
              (d1*d2*g*m+e1*e2*f*(2*p+1)*x+e1*e2*g*(m+2*p+1)*x^2)*(d1+e1*x)^(p-1/2)*(d2+e2*x)^(p-1/2),x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && ILtQ[m,0] && IGtQ[p-1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && iltq!(m_, 0)
                && igtq!(&p_ - Atom::num(1) / Atom::num(2), 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let root = (-&d1__ * &d2__).sqrt();
            let multiplier = &d1__ * &d2__ * &g__ * &m_
                + &e1__ * &e2__ * &f__ * (Atom::num(2) * &p_ + 1) * x_
                + &e1__ * &e2__ * &g__ * (&m_ + Atom::num(2) * &p_ + 1) * x_.pow(2);
            let u = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let v = multiplier * l1.pow(&p_ - Atom::num(1) / Atom::num(2)) * l2.pow(&p_ - Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            let coefficient = Atom::num(1) / (&b__ * &c__ * &root * (&n_ + Atom::num(1)));
            rubi_simp(&(linear.pow(&m_)
                    * l1.pow(&p_ + Atom::num(1) / Atom::num(2))
                    * l2.pow(&p_ + Atom::num(1) / Atom::num(2))
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * &root * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_6394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6394,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          (f+g*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) -
          g*m/(b*c*Sqrt[-d1*d2]*(n+1)) \\[Star] Int[(f+g*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[m,0] && GtQ[d1,0] && LtQ[d2,0] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [g__, m_, a__, b__, c__, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && igtq!(m_, 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let root = (-&d1__ * &d2__).sqrt();
            let recursive = linear.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let coefficient = &g__ * &m_ / (&b__ * &c__ * &root * (&n_ + Atom::num(1)));
            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * &root * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6395,
        source: "Int[(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          1/(c^(m+1)*Sqrt[-d1*d2]) \\[Star] Subst[Int[(a+b*x)^n*(c*f+g*Cosh[x])^m,x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && GtQ[d1,0] && LtQ[d2,0] && (GtQ[m,0] || IGtQ[n,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [g__, m_, a__, b__, c__, n_, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, n_], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(m_)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && (gtq!(m_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * (&c__ * &f__ + &g__ * sub_atom.cosh()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            let coefficient = Atom::num(1) / (c__.pow(&m_ + Atom::num(1)) * (-&d1__ * &d2__).sqrt());
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6396,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),(f+g*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && ILtQ[p+1/2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(m_)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let u = (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_) / (&l1.sqrt() * &l2.sqrt());
            let v = (&f__ + &g__ * x_).pow(&m_)
                * l1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * l2.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6397,
        source: "Int[(f_+g_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/((-1+c*x)^FracPart[p]*(1+c*x)^FracPart[p]) \\[Star]
            Int[(f+g*x)^m*(-1+c*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[m] && IntegerQ[p-1/2] && Not[GtQ[d1,0] && LtQ[d2,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, n_], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(m_)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && !(gtq!(d1__, 0) && ltq!(d2__, 0))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let frac_p_l1 = rubi_frac_part(&p_);
            let frac_p_l2 = rubi_frac_part(&p_);
            let frac_p_left = rubi_frac_part(&p_);
            let frac_p_right = rubi_frac_part(&p_);
            let int_p = rubi_int_part(&p_);
            let transformed = (&f__ + &g__ * x_).pow(&m_)
                * (-Atom::num(1) + &c__ * x_).pow(&p_)
                * (Atom::num(1) + &c__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let coefficient = (-&d1__ * &d2__).pow(int_p)
                * l1.pow(&frac_p_l1)
                * l2.pow(&frac_p_l2)
                / ((-Atom::num(1) + &c__ * x_).pow(&frac_p_left)
                    * (Atom::num(1) + &c__ * x_).pow(&frac_p_right));
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_6398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, h__, m_, n_, x_
    );
    rules.push(rubi_rule!(
        order: 6398,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          Log[h*(f+g*x)^m]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*Sqrt[-d1*d2]*(n+1)) -
          g*m/(b*c*Sqrt[-d1*d2]*(n+1)) \\[Star] Int[(a+b*ArcCosh[c*x])^(n+1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g,h,m},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log()
            * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
            / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt()),
        with: [h__, f__, g__, m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [h__, f__, g__, m_, a__, b__, c__, e1__, e2__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, h__, m_], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &f__ + &g__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = argument.pow(&n_ + Atom::num(1)) / &linear;
            let coefficient = &g__ * &m_
                / (&b__ * &c__ * (-&d1__ * &d2__).sqrt() * (&n_ + Atom::num(1)));
            rubi_simp(&((&h__ * linear.pow(&m_)).log() * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (-&d1__ * &d2__).sqrt() * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, h__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6399,
        source: "Int[Log[h_.*(f_.+g_.*x_)^m_.]*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (-d1*d2)^IntPart[p]*(d1+e1*x)^FracPart[p]*(d2+e2*x)^FracPart[p]/((-1+c*x)^FracPart[p]*(1+c*x)^FracPart[p]) \\[Star]
            Int[Log[h*(f+g*x)^m]*(-1+c*x)^p*(1+c*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g,h,m,n},x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2] && Not[GtQ[d1,0] && LtQ[d2,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (h__ * (f__ + g__ * x_).pow(m_)).log()
            * (d1__ + e1__ * x_).pow(p_)
            * (d2__ + e2__ * x_).pow(p_)
            * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [h__, f__, g__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [h__, f__, g__, m_, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && !(gtq!(d1__, 0) && ltq!(d2__, 0))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let frac_p_l1 = rubi_frac_part(&p_);
            let frac_p_l2 = rubi_frac_part(&p_);
            let frac_p_left = rubi_frac_part(&p_);
            let frac_p_right = rubi_frac_part(&p_);
            let int_p = rubi_int_part(&p_);
            let transformed = (&h__ * (&f__ + &g__ * x_).pow(&m_)).log()
                * (-Atom::num(1) + &c__ * x_).pow(&p_)
                * (Atom::num(1) + &c__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let coefficient = (-&d1__ * &d2__).pow(int_p)
                * l1.pow(&frac_p_l1)
                * l2.pow(&frac_p_l2)
                / ((-Atom::num(1) + &c__ * x_).pow(&frac_p_left)
                    * (Atom::num(1) + &c__ * x_).pow(&frac_p_right));
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_6400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6400,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x)^m*(f+g*x)^m,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[1/(Sqrt[-1+c*x]*Sqrt[1+c*x]) \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[m+1/2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, x_],
        optional: [e__, g__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && iltq!(&m_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&((&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_)), x_).rubi_rhs();
            let reciprocal = Atom::num(1)
                / ((-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt());
            rubi_star(argument, &u)
                    - rubi_star(
                        &b__ * &c__,
                        rubi_rhs_int(&rubi_star(reciprocal, u), x_),
                    )
        },
    ));
}

fn push_rules_rule_6401(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6401,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(d+e*x)^m*(f+g*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [d__, e__, m_, f__, g__, a__, b__, c__, n_, x_],
        optional: [e__, m_, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) && integerq!(m_)
        },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let v = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6402(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 6402,
        source: "Int[u_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcCosh[c*x]) \\[Star] v -
          b*c*Sqrt[1-c^2*x^2]/(Sqrt[-1+c*x]*Sqrt[1+c*x]) \\[Star] Int[SimplifyIntegrand[v/Sqrt[1-c^2*x^2],x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acosh()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let denominator = (-Atom::num(1) + &c__ * x_).sqrt() * (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&v / &radical), x_);
            let coefficient = &b__ * &c__ * radical / denominator;
            rubi_star(argument, v)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6403(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 6403,
        source: "Int[Px_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && PolyQ[Px,x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [px__, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && rubi_poly_q(&px__, x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && {
                    let integrand = &px__
                        * (&d1__ + &e1__ * x_).pow(&p_)
                        * (&d2__ + &e2__ * x_).pow(&p_)
                        * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand = &px__
                * (&d1__ + &e1__ * x_).pow(&p_)
                * (&d2__ + &e2__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6404(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__, m_, n_, p_, px__, x_
    );
    rules.push(rubi_rule!(
        order: 6404,
        source: "Int[Px_.*(f_+g_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[Px*(f+g*(d1+e1*x)^p*(d2+e2*x)^p)^m*(a+b*ArcCosh[c*x])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,g},x] && PolyQ[Px,x] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IGtQ[p+1/2,0] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__
            * (f__ + g__ * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_)).pow(m_)
            * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [px__, f__, g__, d1__, e1__, p_, d2__, e2__, m_, a__, b__, c__, n_, x_],
        optional: [px__, g__, e1__, e2__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, g__], x_)
                && rubi_poly_q(&px__, x_)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && integersq!([m_, n_])
                && {
                    let integrand = &px__
                        * (&f__
                            + &g__ * (&d1__ + &e1__ * x_).pow(&p_) * (&d2__ + &e2__ * x_).pow(&p_))
                            .pow(&m_)
                        * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
                    rubi_expand_integrand_sum(&integrand, x_).is_some()
                }
        },
        rhs: {
            let integrand = &px__
                * (&f__
                    + &g__ * (&d1__ + &e1__ * x_).pow(&p_) * (&d2__ + &e2__ * x_).pow(&p_))
                .pow(&m_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand_sum(&integrand, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6405(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6405,
        source: "Int[RFx_*ArcCosh[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[ArcCosh[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[c,x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (c__ * x_).acosh().pow(n_),
        with: [rfx__, c__, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!(c__, x_) && rubi_rational_function_q(&rfx__, x_) && igtq!(n_, 0)
                && {
                    let u = (&c__ * x_).acosh().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&c__ * x_).acosh().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6406(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6406,
        source: "Int[RFx_*(a_+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[RFx*(a+b*ArcCosh[c*x])^n,x],x] /;
        FreeQ[{a,b,c},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (Atom::var(a_) + b__ * (c__ * x_).acosh()).pow(n_),
        with: [rfx__, a_, b__, c__, n_, x_],
        optional: [b__, c__, n_],
        when: {
            freeq!([a_, b__, c__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
        },
        rhs: {
            let integrand = &rfx__ * (&a_ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6407(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d1__, e1__, d2__, e2__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6407,
        source: "Int[RFx_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*ArcCosh[c_.*x_]^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p*ArcCosh[c*x]^n,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{c,d1,e1,d2,e2},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__ * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (c__ * x_).acosh().pow(n_),
        with: [rfx__, d1__, e1__, p_, d2__, e2__, c__, n_, x_],
        optional: [e1__, e2__, c__, n_],
        when: {
            freeq!([c__, d1__, e1__, d2__, e2__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && {
                    let u = (&d1__ + &e1__ * x_).pow(&p_)
                        * (&d2__ + &e2__ * x_).pow(&p_)
                        * (&c__ * x_).acosh().pow(&n_);
                    rubi_expand_integrand_product_sum(&u, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let u = (&d1__ + &e1__ * x_).pow(&p_)
                * (&d2__ + &e2__ * x_).pow(&p_)
                * (&c__ * x_).acosh().pow(&n_);
            let expanded = rubi_expand_integrand_product_sum(&u, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6408(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d1__, e1__, d2__, e2__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 6408,
        source: "Int[RFx_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(d1+e1*x)^p*(d2+e2*x)^p,RFx*(a+b*ArcCosh[c*x])^n,x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && EqQ[e1-c*d1,0] && EqQ[e2+c*d2,0] && IntegerQ[p-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rfx__
            * (d1__ + e1__ * x_).pow(p_)
            * (d2__ + e2__ * x_).pow(p_)
            * (Atom::var(a_) + b__ * (c__ * x_).acosh()).pow(n_),
        with: [rfx__, d1__, e1__, p_, d2__, e2__, a_, b__, c__, n_, x_],
        optional: [e1__, e2__, b__, c__, n_],
        when: {
            freeq!([a_, b__, c__, d1__, e1__, d2__, e2__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && eqq!(&e1__ - &c__ * &d1__, 0)
                && eqq!(&e2__ + &c__ * &d2__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let u = (&d1__ + &e1__ * x_).pow(&p_) * (&d2__ + &e2__ * x_).pow(&p_);
            let v = &rfx__ * (&a_ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6409(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6409,
        source: "Int[u_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
        },
        rhs: {
            let integrand = u__ * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6377_through_6409_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6377..=6409).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6377..=6409).collect::<Vec<_>>());
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
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
        / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (d1__ + e1__ * x_).pow(p_)
        * (d2__ + e2__ * x_).pow(p_)
        * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}
