use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_240(rules);
    push_rules_rule_241(rules);
    push_rules_rule_242(rules);
    push_rules_rule_243(rules);
    push_rules_rule_244(rules);
    push_rules_rule_245(rules);
    push_rules_rule_246(rules);
    push_rules_rule_247(rules);
    push_rules_rule_248(rules);
    push_rules_rule_249(rules);
    push_rules_rule_250(rules);
    push_rules_rule_251(rules);
    push_rules_rule_252(rules);
    push_rules_rule_253(rules);
    push_rules_rule_254(rules);
    push_rules_rule_255(rules);
    push_rules_rule_256(rules);
    push_rules_rule_257(rules);
    push_rules_rule_258(rules);
    push_rules_rule_259(rules);
    push_rules_rule_260(rules);
    push_rules_rule_261(rules);
    push_rules_rule_262(rules);
    push_rules_rule_263(rules);
    push_rules_rule_264(rules);
    push_rules_rule_265(rules);
    push_rules_rule_266(rules);
    push_rules_rule_267(rules);
    push_rules_rule_268(rules);
    push_rules_rule_269(rules);
    push_rules_rule_270(rules);
    push_rules_rule_271(rules);
    push_rules_rule_272(rules);
    push_rules_rule_273(rules);
    push_rules_rule_274(rules);
    push_rules_rule_275(rules);
    push_rules_rule_276(rules);
    push_rules_rule_277(rules);
    push_rules_rule_278(rules);
    push_rules_rule_279(rules);
}

fn push_rules_rule_240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 240,
        source: "Int[x_/(a_+b_.*x_^2),x_Symbol] :=
          Log[RemoveContent[a+b*x^2,x]]/(2*b) /;
        FreeQ[{a,b},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            rubi_simp(&(rubi_remove_content(&(&a__ + &b__ * x_.pow(2)), x_).log()
                    / (Atom::num(2) * b__)), x_)
        },
    ));
}

fn push_rules_rule_241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 241,
        source: "Int[x_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^(p+1)/(2*b*(p+1)) /;
        FreeQ[{a,b,p},x] && NeQ[p,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__, p_],
        when: { freeq!([a__, b__, p_], x_) && neq!(p_, -1) },
        rhs: {
            rubi_simp(&((&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / (Atom::num(2) * &b__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 242,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*(m+1)) /;
        FreeQ[{a,b,c,m,p},x] && EqQ[m+2*p+3,0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(&((&c__ * x_).pow(&m_ + 1)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / (&a__ * &c__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 243,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(a+b*x)^p,x],x,x^2] /;
        FreeQ[{a,b,m,p},x] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__, m_],
        x_free: [a__, b__, m_, p_],
        when: {
            freeq!([a__, b__, m_, p_], x_)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow((&m_ - 1) / 2) * (&a__ + &b__ * &sub_atom).pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 244,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,m},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_, p_],
        x_free: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__, m_], x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = (&c__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 245,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          x^(m+1)*(a+b*x^2)^(p+1)/(a*(m+1)) -
          b*(m+2*(p+1)+1)/(a*(m+1)) \\[Star] Int[x^(m+2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,m,p},x] && ILtQ[Simplify[(m+1)/2+p+1],0] && NeQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__],
        x_free: [a__, b__, m_, p_],
        when: {
            freeq!([a__, b__, m_, p_], x_)
                && iltq!(rubi_simplify(&((&m_ + 1) / 2 + &p_ + 1)), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = x_.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * (&m_ + 1));
            let primitive = rubi_rhs_int(&(x_.pow(&m_ + 2) * base.pow(&p_)), x_);
            let multiplier = &b__ * (&m_ + Atom::num(2) * (&p_ + 1) + 1)
                / (&a__ * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 246,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*2*(p+1)) +
          (m+2*p+3)/(a*2*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,m,p},x] && ILtQ[Simplify[(m+1)/2+p+1],0] && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && iltq!(rubi_simplify(&((&m_ + 1) / 2 + &p_ + 1)), 0)
                && neq!(p_, -1)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -scaled.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &c__ * Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_) * base.pow(&p_ + 1)), x_);
            let multiplier = (&m_ + Atom::num(2) * &p_ + 3)
                / (&a__ * Atom::num(2) * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 247,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^p/(c*(m+1)) -
          2*b*p/(c^2*(m+1)) \\[Star] Int[(c*x)^(m+2)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c},x] && GtQ[p,0] && LtQ[m,-1] && Not[ILtQ[(m+2*p+3)/2,0]] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && !iltq!((&m_ + Atom::num(2) * &p_ + 3) / 2, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = scaled.pow(&m_ + 1) * base.pow(&p_)
                / (&c__ * (&m_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ + 2) * base.pow(&p_ - 1)), x_);
            let multiplier = Atom::num(2) * &b__ * &p_ / (c__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 248,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^p/(c*(m+2*p+1)) +
          2*a*p/(m+2*p+1) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,m},x] && GtQ[p,0] && NeQ[m+2*p+1,0] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let direct = scaled.pow(&m_ + 1) * base.pow(&p_)
                / (&c__ * &denominator);
            let primitive = rubi_rhs_int(&(scaled.pow(&m_) * base.pow(&p_ - 1)), x_);
            let multiplier = Atom::num(2) * &a__ * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 249,
        source: "Int[Sqrt[c_.*x_]/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
          Sqrt[c*x]*(1+a/(b*x^2))^(1/4)/(b*(a+b*x^2)^(1/4)) \\[Star] Int[1/(x^2*(1+a/(b*x^2))^(5/4)),x] /;
        FreeQ[{a,b,c},x] && PosQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ * x_).sqrt() / (a__ + b__ * x_.pow(2)).pow((5, 4)),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &a__ / (&b__ * x_.pow(2));
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (x_.pow(2) * normalized.pow((5, 4)))),
                x_,
            );
            let multiplier = (&c__ * x_).sqrt() * normalized.pow((1, 4))
                / (&b__ * base.pow((1, 4)));
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 250,
        source: "Int[(c_.*x_)^m_/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
          2*c*(c*x)^(m-1)/(b*(2*m-3)*(a+b*x^2)^(1/4)) - 2*a*c^2*(m-1)/(b*(2*m-3)) \\[Star] Int[(c*x)^(m-2)/(a+b*x^2)^(5/4),x] /;
        FreeQ[{a,b,c},x] && PosQ[b/a] && IntegerQ[2*m] && GtQ[m,3/2]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && posq!(&b__ / &a__)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, Atom::num((3, 2)))
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = Atom::num(2) * &c__ * scaled.pow(&m_ - 1)
                / (&b__ * (Atom::num(2) * &m_ - 3) * base.pow((1, 4)));
            let primitive = rubi_rhs_int(
                &(scaled.pow(&m_ - 2) / base.pow((5, 4))),
                x_,
            );
            let multiplier = Atom::num(2) * &a__ * c__.pow(2) * (&m_ - 1)
                / (&b__ * (Atom::num(2) * &m_ - 3));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 251,
        source: "Int[(c_.*x_)^m_/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
          (c*x)^(m+1)/(a*c*(m+1)*(a+b*x^2)^(1/4)) - b*(2*m+1)/(2*a*c^2*(m+1)) \\[Star] Int[(c*x)^(m+2)/(a+b*x^2)^(5/4),x] /;
        FreeQ[{a,b,c},x] && PosQ[b/a] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && posq!(&b__ / &a__)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = scaled.pow(&m_ + 1)
                / (&a__ * &c__ * (&m_ + 1) * base.pow((1, 4)));
            let primitive = rubi_rhs_int(
                &(scaled.pow(&m_ + 2) / base.pow((5, 4))),
                x_,
            );
            let multiplier = &b__ * (Atom::num(2) * &m_ + 1)
                / (Atom::num(2) * &a__ * c__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 252,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*(c*x)^(m-1)*(a+b*x^2)^(p+1)/(2*b*(p+1)) -
          c^2*(m-1)/(2*b*(p+1)) \\[Star] Int[(c*x)^(m-2)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c},x] && LtQ[p,-1] && GtQ[m,1] && Not[ILtQ[(m+2*p+3)/2,0]] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && !iltq!((&m_ + Atom::num(2) * &p_ + 3) / 2, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = &c__ * scaled.pow(&m_ - 1) * base.pow(&p_ + 1)
                / (Atom::num(2) * &b__ * (&p_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ - 2) * base.pow(&p_ + 1)), x_);
            let multiplier = c__.pow(2) * (&m_ - 1)
                / (Atom::num(2) * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 253,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^2)^(p+1)/(2*a*c*(p+1)) +
          (m+2*p+3)/(2*a*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,m},x] && LtQ[p,-1] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && ltq!(p_, -1)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -scaled.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &c__ * (&p_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_) * base.pow(&p_ + 1)), x_);
            let multiplier = (&m_ + Atom::num(2) * &p_ + 3)
                / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 254,
        source: "Int[x_^m_/(a_+b_.*x_^2),x_Symbol] :=
          Int[PolynomialDivide[x^m,(a+b*x^2),x],x] /;
        FreeQ[{a,b},x] && IGtQ[m,3]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, m_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && igtq!(m_, 3) },
        rhs: {
            let divided = rubi_polynomial_divide(
                x_.pow(&m_),
                &(&a__ + &b__ * x_.pow(2)),
                x_,
            ).rubi_rhs();
            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 255,
        source: "Int[Sqrt[c_*x_]/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          x*Sqrt[c*x]/(a+b*x^2)^(1/4) - a/2 \\[Star] Int[Sqrt[c*x]/(a+b*x^2)^(5/4),x] /;
        FreeQ[{a,b,c},x] && PosQ[b/a]",
        desc: "Binomial recurrence 1b",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = x_ * &scaled.sqrt() / base.pow((1, 4));
            let primitive = rubi_rhs_int(&(scaled.sqrt() / base.pow((5, 4))), x_);
            rubi_simp(&(direct), x_) - rubi_star(&a__ / 2, primitive)
        },
    ));
}

fn push_rules_rule_256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 256,
        source: "Int[Sqrt[c_*x_]/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          c*(a+b*x^2)^(3/4)/(b*Sqrt[c*x]) + a*c^2/(2*b) \\[Star] Int[1/((c*x)^(3/2)*(a+b*x^2)^(1/4)),x] /;
        FreeQ[{a,b,c},x] && NegQ[b/a]",
        desc: "Binomial recurrence 3a",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && negq!(&b__ / &a__) },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = &c__ * base.pow((3, 4)) / (&b__ * &scaled.sqrt());
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (scaled.pow((3, 2)) * base.pow((1, 4)))),
                x_,
            );
            let multiplier = &a__ * c__.pow(2) / (Atom::num(2) * &b__);
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 257,
        source: "Int[1/((c_.*x_)^(3/2)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
          -2/(c*Sqrt[c*x]*(a+b*x^2)^(1/4)) - b/c^2 \\[Star] Int[Sqrt[c*x]/(a+b*x^2)^(5/4),x] /;
        FreeQ[{a,b,c},x] && PosQ[b/a]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.3"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -Atom::num(2) / (&c__ * &scaled.sqrt() * base.pow((1, 4)));
            let primitive = rubi_rhs_int(&(scaled.sqrt() / base.pow((5, 4))), x_);
            rubi_simp(&(direct), x_) - rubi_star(&b__ / c__.pow(2), primitive)
        },
    ));
}

fn push_rules_rule_258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 258,
        source: "Int[1/((c_.*x_)^(3/2)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
          Sqrt[c*x]*(1+a/(b*x^2))^(1/4)/(c^2*(a+b*x^2)^(1/4)) \\[Star] Int[1/(x^2*(1+a/(b*x^2))^(1/4)),x] /;
        FreeQ[{a,b,c},x] && NegQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && negq!(&b__ / &a__) },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &a__ / (&b__ * x_.pow(2));
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (x_.pow(2) * normalized.pow((1, 4)))),
                x_,
            );
            let multiplier = scaled.sqrt() * normalized.pow((1, 4))
                / (c__.pow(2) * base.pow((1, 4)));
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 259,
        source: "Int[Sqrt[x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          -2/(Sqrt[a]*(-b/a)^(3/4)) \\[Star] Subst[Int[Sqrt[1-2*x^2]/Sqrt[1-x^2],x],x,Sqrt[1-Sqrt[-b/a]*x]/Sqrt[2]] /;
        FreeQ[{a,b},x] && GtQ[-b/a,0] && GtQ[a,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_) && gtq!(-&b__ / &a__, 0) && gtq!(a__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((Atom::num(1) - Atom::num(2) * sub_atom.pow(2)).sqrt()
                    / (Atom::num(1) - sub_atom.pow(2)).sqrt()),
                sub,
            );
            let replacement = (Atom::num(1) - (-&b__ / &a__).sqrt() * x_).sqrt()
                / Atom::num(2).sqrt();
            let multiplier = -Atom::num(2) / (a__.sqrt() * (-&b__ / &a__).pow((3, 4)));
            rubi_star(multiplier, rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 260,
        source: "Int[Sqrt[x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[Sqrt[x]/Sqrt[1+b*x^2/a],x] /;
        FreeQ[{a,b},x] && GtQ[-b/a,0] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_) && gtq!(-&b__ / &a__, 0) && !gtq!(a__, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(&(x_.sqrt() / &normalized.sqrt()), x_);
            let multiplier = normalized.sqrt() / base.sqrt();
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 261,
        source: "Int[Sqrt[c_*x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          Sqrt[c*x]/Sqrt[x] \\[Star] Int[Sqrt[x]/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c},x] && GtQ[-b/a,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ * x_).sqrt() / (a__ + b__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, x_],
        optional: [b__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && gtq!(-&b__ / &a__, 0) },
        rhs: {
            let primitive = rubi_rhs_int(
                &(x_.sqrt() / (&a__ + &b__ * x_.pow(2)).sqrt()),
                x_,
            );
            let multiplier = (&c__ * x_).sqrt() / x_.sqrt();
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 262,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*(c*x)^(m-1)*(a+b*x^2)^(p+1)/(b*(m+2*p+1)) -
          a*c^2*(m-1)/(b*(m+2*p+1)) \\[Star] Int[(c*x)^(m-2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,p},x] && GtQ[m,2-1] && NeQ[m+2*p+1,0] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let direct = &c__ * scaled.pow(&m_ - 1) * base.pow(&p_ + 1)
                / (&b__ * &denominator);
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ - 2) * base.pow(&p_)), x_);
            let multiplier = &a__ * c__.pow(2) * (&m_ - 1) / (&b__ * denominator);
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 263,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c*(c*x)^(m-1)*(a+b*x^2)^(p+1)/(b*(m+2*p+1)) -
          a*c^2*(m-1)/(b*(m+2*p+1)) \\[Star] Int[(c*x)^(m-2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && SumSimplerQ[m,-2] && NeQ[m+2*p+1,0] && ILtQ[Simplify[(m+1)/2+p],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && sum_simplerq!(m_, -2)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && iltq!(rubi_simplify(&((&m_ + 1) / 2 + &p_)), 0)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let direct = &c__ * scaled.pow(&m_ - 1) * base.pow(&p_ + 1)
                / (&b__ * &denominator);
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ - 2) * base.pow(&p_)), x_);
            let multiplier = &a__ * c__.pow(2) * (&m_ - 1) / (&b__ * denominator);
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 264,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*(m+1)) -
          b*(m+2*p+3)/(a*c^2*(m+1)) \\[Star] Int[(c*x)^(m+2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,p},x] && LtQ[m,-1] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && ltq!(m_, -1)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = scaled.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &c__ * (&m_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ + 2) * base.pow(&p_)), x_);
            let multiplier = &b__ * (&m_ + Atom::num(2) * &p_ + 3)
                / (&a__ * c__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 265,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*(m+1)) -
          b*(m+2*p+3)/(a*c^2*(m+1)) \\[Star] Int[(c*x)^(m+2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && SumSimplerQ[m,2] && ILtQ[Simplify[(m+1)/2+p],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && sum_simplerq!(m_, 2)
                && iltq!(rubi_simplify(&((&m_ + 1) / 2 + &p_)), 0)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = scaled.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &c__ * (&m_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_ + 2) * base.pow(&p_)), x_);
            let multiplier = &b__ * (&m_ + Atom::num(2) * &p_ + 3)
                / (&a__ * c__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 266,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/c \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(2*k)/c^2)^p,x],x,(c*x)^(1/k)]] /;
        FreeQ[{a,b,c,p},x] && FractionQ[m] && IntBinomialQ[a,b,c,2,m,p,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && fractionq!(m_)
                && rubi_int_binomial_q(&a__, &b__, &c__, &Atom::num(2), &m_, &p_, x_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&k * (&m_ + 1) - 1)
                    * (&a__ + &b__ * sub_atom.pow(Atom::num(2) * &k) / c__.pow(2)).pow(&p_)),
                sub,
            );
            let replacement = (&c__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&primitive, sub, replacement);
            rubi_star(&k / &c__, substituted)
        },
    ));
}

fn push_rules_rule_267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 267,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^(p+(m+1)/2) \\[Star] Subst[Int[x^m/(1-b*x^2)^(p+(m+1)/2+1),x],x,x/(a+b*x^2)^(1/2)] /;
        FreeQ[{a,b},x] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegersQ[m,p+(m+1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__, m_],
        x_free: [a__, b__],
        when: {
            let shift = &p_ + (&m_ + 1) / 2;
            freeq!([a__, b__], x_)
                && ltq!(-1, p_, 0)
                && neq!(p_, Atom::num((-1, 2)))
                && integersq!([m_, shift])
        },
        rhs: {
            let shift = &p_ + (&m_ + 1) / 2;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&m_)
                    / (Atom::num(1) - &b__ * sub_atom.pow(2)).pow(&shift + 1)),
                sub,
            );
            let replacement = x_ / (&a__ + &b__ * x_.pow(2)).sqrt();
            rubi_star(a__.pow(shift), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 268,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a/(a+b*x^2))^(p+(m+1)/2)*(a+b*x^2)^(p+(m+1)/2) \\[Star] Subst[Int[x^m/(1-b*x^2)^(p+(m+1)/2+1),x],x,x/(a+b*x^2)^(1/2)] /;
        FreeQ[{a,b},x] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegerQ[m] && LtQ[Denominator[p+(m+1)/2],Denominator[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__, m_],
        x_free: [a__, b__],
        when: {
            let shift = &p_ + (&m_ + 1) / 2;
            freeq!([a__, b__], x_)
                && ltq!(-1, p_, 0)
                && neq!(p_, Atom::num((-1, 2)))
                && integerq!(m_)
                && ltq!(
                    rubi_denominator_atom(&shift),
                    rubi_denominator_atom(&p_)
                )
        },
        rhs: {
            let shift = &p_ + (&m_ + 1) / 2;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&m_)
                    / (Atom::num(1) - &b__ * sub_atom.pow(2)).pow(&shift + 1)),
                sub,
            );
            let base = &a__ + &b__ * x_.pow(2);
            let replacement = x_ / &base.sqrt();
            let multiplier = (&a__ / &base).pow(&shift) * base.pow(&shift);
            rubi_star(multiplier, rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 269,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          x^(m+1)*(a+b*x^2)^p/(m+1) -
          2*b*p/(m+1) \\[Star] Int[x^(m+2)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,m},x] && EqQ[(m+1)/2+p,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__, m_],
        x_free: [a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && eqq!((&m_ + 1) / 2 + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = x_.pow(&m_ + 1) * base.pow(&p_) / (&m_ + 1);
            let primitive = rubi_rhs_int(&(x_.pow(&m_ + 2) * base.pow(&p_ - 1)), x_);
            let multiplier = Atom::num(2) * &b__ * &p_ / (&m_ + 1);
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 270,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,m},x] && EqQ[(m+1)/2+p,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && eqq!((&m_ + 1) / 2 + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_))
                * (&c__ * x_).pow(&frac)
                / x_.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 271,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^2)^p/(c*(m+2*p+1)) +
          2*a*p/(m+2*p+1) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,m},x] && IntegerQ[p+Simplify[(m+1)/2]] && GtQ[p,0] && NeQ[m+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && integerq!(&p_ + rubi_simplify(&((&m_ + 1) / 2)))
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let direct = scaled.pow(&m_ + 1) * base.pow(&p_)
                / (&c__ * &denominator);
            let primitive = rubi_rhs_int(&(scaled.pow(&m_) * base.pow(&p_ - 1)), x_);
            let multiplier = Atom::num(2) * &a__ * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 272,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{k=Denominator[p]},
          k*a^(p+Simplify[(m+1)/2])/2 \\[Star]
            Subst[Int[x^(k*Simplify[(m+1)/2]-1)/(1-b*x^k)^(p+Simplify[(m+1)/2]+1),x],x,x^(2/k)/(a+b*x^2)^(1/k)]] /;
        FreeQ[{a,b,m},x] && IntegerQ[p+Simplify[(m+1)/2]] && LtQ[-1,p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, m_, p_, x_],
        optional: [b__, m_],
        x_free: [a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && integerq!(&p_ + rubi_simplify(&((&m_ + 1) / 2)))
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&p_).rubi_rhs());
            let half = rubi_simplify(&((&m_ + 1) / 2));
            let shift = &p_ + &half;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&k * &half - 1)
                    / (Atom::num(1) - &b__ * sub_atom.pow(&k)).pow(&shift + 1)),
                sub,
            );
            let base = &a__ + &b__ * x_.pow(2);
            let replacement = x_.pow(Atom::num(2) / &k) / base.pow(Atom::num(1) / &k);
            let multiplier = &k * a__.pow(shift) / 2;
            rubi_star(multiplier, rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 273,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,m},x] && IntegerQ[p+Simplify[(m+1)/2]] && LtQ[-1,p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && integerq!(&p_ + rubi_simplify(&((&m_ + 1) / 2)))
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_))
                * (&c__ * x_).pow(&frac)
                / x_.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 274,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*2*(p+1)) +
          (m+2*(p+1)+1)/(a*2*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,m},x] && IntegerQ[p+Simplify[(m+1)/2]] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && integerq!(&p_ + rubi_simplify(&((&m_ + 1) / 2)))
                && ltq!(p_, -1)
        },
        rhs: {
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -scaled.pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &c__ * Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&(scaled.pow(&m_) * base.pow(&p_ + 1)), x_);
            let multiplier = (&m_ + Atom::num(2) * (&p_ + 1) + 1)
                / (&a__ * Atom::num(2) * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 275,
        source: "Int[x_^m_./(a_+b_.*x_^2),x_Symbol] :=
          x^(m-1)/(b*(m-1)) -
          a/b \\[Star] Int[x^(m-2)/(a+b*x^2),x] /;
        FreeQ[{a,b,m},x] && FractionQ[(m+1)/2] && SumSimplerQ[m,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, m_, x_],
        optional: [b__, m_],
        x_free: [a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && fractionq!((&m_ + 1) / 2)
                && sum_simplerq!(m_, -2)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = x_.pow(&m_ - 1) / (&b__ * (&m_ - 1));
            let primitive = rubi_rhs_int(&(x_.pow(&m_ - 2) / base), x_);
            rubi_simp(&(direct), x_) - rubi_star(&a__ / &b__, primitive)
        },
    ));
}

fn push_rules_rule_276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 276,
        source: "Int[x_^m_/(a_+b_.*x_^2),x_Symbol] :=
          x^(m+1)/(a*(m+1)) -
          b/a \\[Star] Int[x^Simplify[m+2]/(a+b*x^2),x] /;
        FreeQ[{a,b,m},x] && FractionQ[(m+1)/2] && SumSimplerQ[m,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, m_, x_],
        optional: [b__],
        x_free: [a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && fractionq!((&m_ + 1) / 2)
                && sum_simplerq!(m_, 2)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = x_.pow(&m_ + 1) / (&a__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &(x_.pow(rubi_simplify(&(&m_ + 2))) / base),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(&b__ / &a__, primitive)
        },
    ));
}

fn push_rules_rule_277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 277,
        source: "Int[(c_*x_)^m_/(a_+b_.*x_^2),x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m/(a+b*x^2),x] /;
        FreeQ[{a,b,c,m},x] && FractionQ[(m+1)/2] && (SumSimplerQ[m,2] || SumSimplerQ[m,-2])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ * x_).pow(m_) / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, m_, x_],
        optional: [b__],
        x_free: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && fractionq!((&m_ + 1) / 2)
                && (sum_simplerq!(m_, 2) || sum_simplerq!(m_, -2))
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_))
                * (&c__ * x_).pow(&frac)
                / x_.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 278,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^p*(c*x)^(m+1)/(c*(m+1))*Hypergeometric2F1[-p,(m+1)/2,(m+1)/2+1,-b*x^2/a] /;
        FreeQ[{a,b,c,m,p},x] && Not[IGtQ[p,0]] && (ILtQ[p,0] || GtQ[a,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && !igtq!(p_, 0)
                && (iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let shifted = &m_ + 1;
            rubi_simp(&(a__.pow(&p_)
                    * (&c__ * x_).pow(&shifted)
                    / (&c__ * &shifted)
                    * rubi_hypergeometric2f1(
                        -&p_,
                        &shifted / 2,
                        &shifted / 2 + 1,
                        -&b__ * x_.pow(2) / &a__,
                    )), x_)
        },
    ));
}

fn push_rules_rule_279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 279,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^2)^FracPart[p]/(1+b*x^2/a)^FracPart[p] \\[Star] Int[(c*x)^m*(1+b*x^2/a)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && Not[IGtQ[p,0]] && Not[ILtQ[p,0] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && !igtq!(p_, 0)
                && !(iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(
                &((&c__ * x_).pow(&m_) * normalized.pow(&p_)),
                x_,
            );
            let frac = rubi_frac_part(&p_);
            let multiplier = a__.pow(rubi_int_part(&p_)) * base.pow(&frac)
                / normalized.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) / (a__ + b__ * x_.pow(2)).pow((5, 4))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    (c__ * x_).sqrt() / (a__ + b__ * x_.pow(2)).pow((1, 4))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    Atom::num(1) / ((c__ * x_).pow((3, 2)) * (a__ + b__ * x_.pow(2)).pow((1, 4)))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_.pow((1, 2)) / (a__ + b__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ + b__ * x_.pow(2))
}
