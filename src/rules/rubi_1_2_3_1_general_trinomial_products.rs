use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1679(rules);
    push_rules_rule_1680(rules);
    push_rules_rule_1681(rules);
    push_rules_rule_1379(rules);
    push_rules_rule_1682(rules);
    push_rules_rule_1683(rules);
    push_rules_rule_1684(rules);
    push_rules_rule_1685(rules);
    push_rules_rule_1686(rules);
    push_rules_rule_1687(rules);
    push_rules_rule_1688(rules);
    push_rules_rule_1689(rules);
}

fn push_rules_rule_1679(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1679,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[x^(2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && LtQ[n,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && ltq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(2) * &n_ * &p_)
                * (&c__ + &b__ * x_.pow(-&n_) + &a__ * x_.pow(Atom::num(-2) * &n_))
                    .pow(p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1680(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1680,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__
                    + &b__ * sub_atom.pow(&k * &n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &k * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                x_.pow(Atom::num(1) / k_i),
            );

            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_1681(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1681,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && ILtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__
                + &b__ * sub_atom.pow(-&n_)
                + &c__ * sub_atom.pow(Atom::num(-2) * &n_))
            .pow(&p_)
                / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1379,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/c^p \\[Star] Int[(b/2+c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p] && NeQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
                && neq!(p_, 1)
        },
        rhs: {
            let recursive_integrand =
                (&b__ / Atom::num(2) + &c__ * x_.pow(&n_)).pow(Atom::num(2) * &p_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1682(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1682,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1683(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1683,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -x*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(b^2-2*a*c+n*(p+1)*(b^2-4*a*c)+b*c*(n*(2*p+3)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[p,-1]",
        desc: "Trinomial recurrence 2b with m=0, A=1 and B=0",
        refs: ["G&R 2.161.5"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(p_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p1 = &p_ + Atom::num(1);
            let denominator = &a__ * &n_ * &p1 * &discriminant;
            let direct = Atom::num(-1) * x_
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_))
                * trinomial.pow(&p1)
                / &denominator;
            let recursive_integrand = (b__.pow(2) - Atom::num(2) * &a__ * &c__
                + &n_ * &p1 * &discriminant
                + &b__
                    * &c__
                    * (&n_ * (Atom::num(2) * &p_ + Atom::num(3)) + Atom::num(1))
                    * x_.pow(&n_))
                * trinomial.pow(p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1684(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1684,
        source: "Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*q*r) \\[Star] Int[(r-x^(n/2))/(q-r*x^(n/2)+x^n),x] +
          1/(2*c*q*r) \\[Star] Int[(r+x^(n/2))/(q+r*x^(n/2)+x^n),x]]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n/2,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, c__, n2_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let denominator = Atom::num(2) * &c__ * &q * &r;
            let first_integrand = (&r - &half_power) / (&q - &r * &half_power + x_.pow(&n_));
            let second_integrand = (&r + &half_power) / (&q + &r * &half_power + x_.pow(n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &denominator, first)
                    + rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_1685(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1685,
        source: "Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          c/q \\[Star] Int[1/(b/2-q/2+c*x^n),x] - c/q \\[Star] Int[1/(b/2+q/2+c*x^n),x]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, c__, n2_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&c__ / &q, first)
                    + rubi_star(-&c__ / q, second)
        },
    ));
}

fn push_rules_rule_1686(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1686,
        source: "Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
            ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p]) \\[Star]
            Int[(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let sqrt_discriminant = discriminant.sqrt();
            let int_p = rubi_int_part(&p_);
            let frac_p = rubi_frac_part(&p_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let first = Atom::num(1)
                + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ + &sqrt_discriminant);
            let second = Atom::num(1)
                + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ - &sqrt_discriminant);
            let recursive = rubi_rhs_int(&(first.pow(&p_) * second.pow(&p_)), x_);
            let denominator = (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ + &q))
                .pow(&frac_p)
                * (Atom::num(1) + Atom::num(2) * &c__ * x_.pow(n_) / (&b__ - q))
                    .pow(&frac_p);
            let coefficient = a__.pow(int_p) * trinomial.pow(frac_p) / denominator;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1687(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, p_, u__);
    rules.push(rubi_rule!(
        order: 1687,
        source: "Int[(a_+b_.*u_^n_+c_.*u_^n2_.)^p_,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__.pow(n_) + c__ * u__.pow(n2_)).pow(p_),
        with: [a__, b__, u__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_dep: [],
        x_free: [a__, b__, c__, n_, p_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coeff(&u__, x_, 1).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__
                + &b__ * sub_atom.pow(&n_)
                + &c__ * sub_atom.pow(Atom::num(2) * &n_))
            .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / coefficient, substituted)
        },
    ));
}

fn push_rules_rule_1688(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, mn_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1688,
        source: "Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_,x_Symbol] :=
          Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
        FreeQ[{a,b,c,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, mn_, c__, n_, p_, x_],
        optional: [b__, c__, n_],
        x_free: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
                && posq!(n_)
        },
        rhs: {
            let recursive_integrand = (&b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                .pow(&p_)
                / x_.pow(&n_ * &p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1689(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, mn_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1689,
        source: "Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_,x_Symbol] :=
          x^(n*FracPart[p])*(a+b*x^(-n)+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p] \\[Star] Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, mn_, c__, n_, p_, x_],
        optional: [b__, c__, n_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(p_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let original = &a__ + &b__ * x_.pow(-&n_) + &c__ * x_.pow(&n_);
            let transformed = &b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = transformed.pow(&p_) / x_.pow(&n_ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(&n_ * &frac_p) * original.pow(&frac_p)
                / transformed.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}
