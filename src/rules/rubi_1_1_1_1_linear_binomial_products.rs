use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_14(rules);
    push_rules_rule_15(rules);
    push_rules_rule_16(rules);
    push_rules_rule_17(rules);
    push_rules_rule_18(rules);
    push_rules_rule_19(rules);
    push_rules_rule_20(rules);
    push_rules_rule_21(rules);
    push_rules_rule_22(rules);
    push_rules_rule_23(rules);
    push_rules_rule_28(rules);
    push_rules_rule_29(rules);
    push_rules_rule_30(rules);
    push_rules_rule_31(rules);
    push_rules_rule_32(rules);
    push_rules_rule_33(rules);
    push_rules_rule_34(rules);
}

fn push_rules_rule_14(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, x_);
    rules.push(rubi_rule!(
        order: 14,
        source: "Int[a_./x_,x_Symbol] :=
          a*Log[x] /;
        FreeQ[a,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: a__ * x_.pow(-1),
        with: [a__, x_],
        optional: [a__],
        x_free: [a__],
        when: { freeq!(a__, x_) },
        rhs: { rubi_simp(&(a__ * x_.log()), x_) },
    ));
}

fn push_rules_rule_15(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, x_);
    rules.push(rubi_rule!(
        order: 15,
        source: "Int[a_.*x_^m_.,x_Symbol] :=
          a*x^(m+1)/(m+1) /;
        FreeQ[{a,m},x] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: a__ * x_.pow(m_),
        with: [a__, m_, x_],
        optional: [a__, m_],
        x_free: [a__, m_],
        when: { freeq!([a__, m_], x_) && neq!(m_, -Atom::num(1)) },
        rhs: {
            let m1 = m_ + Atom::num(1);
            rubi_simp(&(a__ * x_.pow(&m1) / m1), x_)
        },
    ));
}

fn push_rules_rule_16(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 16,
        source: "Int[c_./(a_.+b_.*x_),x_Symbol] :=
          c*Log[RemoveContent[a+b*x,x]]/b /;
        FreeQ[{a,b,c},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: c__ * (a__ + b__ * x_).pow(-1),
        with: [c__, a__, b__, x_],
        optional: [c__, a__, b__],
        x_free: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            rubi_simp(&(c__ * rubi_remove_content(&(a__ + &b__ * x_), x_).log() / b__), x_)
        },
    ));
}

fn push_rules_rule_17(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 17,
        source: "Int[c_.*(a_.+b_.*x_)^m_.,x_Symbol] :=
          c*(a+b*x)^(m+1)/(b*(m+1)) /;
        FreeQ[{a,b,c,m},x] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: c__ * (a__ + b__ * x_).pow(m_),
        with: [c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        x_free: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__, m_], x_) && neq!(m_, -Atom::num(1)) },
        rhs: {
            let m1 = m_ + Atom::num(1);
            rubi_simp(&(c__ * (a__ + &b__ * x_).pow(&m1) / (b__ * m1)), x_)
        },
    ));
}

fn push_rules_rule_18(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__);
    rules.push(rubi_rule!(
        order: 18,
        source: "Int[c_.*(a_.+b_.*u_)^m_,x_Symbol] :=
          1/D[u,x] \\[Star] Subst[Int[c*(a+b*x)^m,x],x,u] /;
        FreeQ[{a,b,c,m},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: c__ * (a__ + b__ * u__).pow(m_),
        with: [c__, a__, b__, u__, m_, x_],
        optional: [c__, a__, b__],
        x_dep: [],
        x_free: [a__, b__, c__, m_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, m_], x_) && neq!(u__, x_)
        },
        rhs: {
            let Some((_u0, u1)) = linear_coefficients(&u__, x_) else {
                panic!("Rubi RHS invariant was not established by the rule condition");
            };
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(&(c__ * (a__ + b__ * &sub).pow(m_)), sub_symbol);
            rubi_star(Atom::num(1) / u1, substitute_symbol(&primitive, sub_symbol, u__))
        },
    ));
}

fn push_rules_rule_19(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, p_, x_);
    rules.push(rubi_rule!(
        order: 19,
        source: "Int[(a_./x_)^p_,x_Symbol] :=
          -a*(a/x)^(p-1)/(p-1) /;
        FreeQ[{a,p},x] && Not[IntegerQ[p]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ / x_).pow(p_),
        with: [a__, p_, x_],
        optional: [a__],
        x_free: [a__, p_],
        when: { freeq!([a__, p_], x_) && !integerq!(p_) },
        rhs: {
            rubi_simp(&(-&a__ * (a__ / x_).pow(&p_ - Atom::num(1))
                    / (&p_ - Atom::num(1))), x_)
        },
    ));
}

fn push_rules_rule_20(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 20,
        source: "Int[(a_.*x_^n_)^p_,x_Symbol] :=
          (a*x^n)^p/x^(n*p) \\[Star] Int[x^(n*p),x] /;
        FreeQ[{a,n,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(n_)).pow(p_),
        with: [a__, n_, p_, x_],
        optional: [a__],
        x_free: [a__, n_, p_],
        when: { freeq!([a__, n_, p_], x_) && !integerq!(p_) },
        rhs: {
            let multiplier = (&a__ * x_.pow(&n_)).pow(&p_) / x_.pow(&n_ * &p_);
            rubi_star(multiplier, rubi_rhs_int(x_.pow(&n_ * &p_), x_))
        },
    ));
}

fn push_rules_rule_21(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 21,
        source: "Int[x_^m_.*(a_.*x_^n_)^p_,x_Symbol] :=
          1/(n*a^(Simplify[(m+1)/n]-1)) \\[Star] Subst[Int[(a*x)^(Simplify[(m+1)/n]+p-1),x],x,x^n] /;
        FreeQ[{a,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, n_, p_, x_],
        optional: [m_, a__],
        x_free: [a__, m_, n_, p_],
        when: {
            freeq!([a__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let primitive = rubi_rhs_int(
                &(&a__ * &sub).pow(&substitution_exponent + &p_ - Atom::num(1)),
                sub_symbol,
            );
            let substituted = substitute_symbol(
                &primitive,
                sub_symbol,
                x_.pow(&n_),
            );
            rubi_star(Atom::num(1) / (&n_ * a__.pow(&substitution_exponent - Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_22(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 22,
        source: "Int[x_^m_.*(a_.*x_^n_.)^p_,x_Symbol] :=
          1/a^(m/n) \\[Star] Int[(a*x^n)^(p+m/n),x] /;
        FreeQ[{a,m,n,p},x] && IntegerQ[m/n] && LtQ[p*m/n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, n_, p_, x_],
        optional: [m_, a__, n_],
        x_free: [a__, m_, n_, p_],
        when: {
            freeq!([a__, m_, n_, p_], x_)
                && integerq!(&m_ / &n_)
                && ltq!(&p_ * &m_ / &n_, 0)
        },
        rhs: {
            let quotient = &m_ / &n_;
            rubi_star(Atom::num(1) / a__.pow(&quotient), rubi_rhs_int(
                    &(&a__ * x_.pow(&n_)).pow(&p_ + &quotient),
                    x_,
                ))
        },
    ));
}

fn push_rules_rule_23(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 23,
        source: "Int[x_^m_.*(a_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^n)^p/x^(n*p) \\[Star] Int[x^(m+n*p),x] /;
        FreeQ[{a,m,n,p},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, n_, p_, x_],
        optional: [m_, a__, n_],
        x_free: [a__, m_, n_, p_],
        when: { freeq!([a__, m_, n_, p_], x_) },
        rhs: {
            let multiplier = (&a__ * x_.pow(&n_)).pow(&p_)
                / x_.pow(&n_ * &p_);
            rubi_star(multiplier, rubi_rhs_int(x_.pow(&m_ + &n_ * &p_), x_))
        },
    ));
}

fn push_rules_rule_28(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, i_, j_, k_, m_, p_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 28,
        source: "Int[u_.*(a_.*x_)^m_.*(b_.*x_^i_.)^p_.*(c_.*x_^j_.)^q_.*(d_.*x_^k_.)^r_.,x_Symbol] :=
          (b*x^i)^p*(c*x^j)^q*(d*x^k)^r/(a*x)^(i*p+j*q+k*r) \\[Star] Int[u*(a*x)^(m+i*p+j*q+k*r),x] /;
        FreeQ[{a,b,c,d,i,j,k,m,p,q,r},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (a__ * x_).pow(m_)
            * (b__ * x_.pow(i_)).pow(p_)
            * (c__ * x_.pow(j_)).pow(q_)
            * (d__ * x_.pow(k_)).pow(r_),
        with: [u__, a__, m_, b__, i_, p_, c__, j_, q_, d__, k_, r_, x_],
        optional: [u__, a__, m_, b__, i_, p_, c__, j_, q_, d__, k_, r_],
        x_free: [a__, b__, c__, d__, i_, j_, k_, m_, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, i_, j_, k_, m_, p_, q_, r_], x_) },
        rhs: {
            let exponent = &i_ * &p_ + &j_ * &q_ + &k_ * &r_;
            let multiplier = (&b__ * x_.pow(&i_)).pow(&p_)
                * (&c__ * x_.pow(&j_)).pow(&q_)
                * (&d__ * x_.pow(&k_)).pow(&r_)
                / (&a__ * x_).pow(&exponent);
            rubi_star(multiplier, rubi_rhs_int(
                        &(u__ * (&a__ * x_).pow(&m_ + exponent)),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_29(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, i_, j_, m_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 29,
        source: "Int[u_.*(a_.*x_)^m_.*(b_.*x_^i_.)^p_.*(c_.*x_^j_.)^q_.,x_Symbol] :=
          (b*x^i)^p*(c*x^j)^q/(a*x)^(i*p+j*q) \\[Star] Int[u*(a*x)^(m+i*p+j*q),x] /;
        FreeQ[{a,b,c,i,j,m,p,q},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (a__ * x_).pow(m_)
            * (b__ * x_.pow(i_)).pow(p_)
            * (c__ * x_.pow(j_)).pow(q_),
        with: [u__, a__, m_, b__, i_, p_, c__, j_, q_, x_],
        optional: [u__, a__, m_, b__, i_, p_, c__, j_, q_],
        x_free: [a__, b__, c__, i_, j_, m_, p_, q_],
        when: { freeq!([a__, b__, c__, i_, j_, m_, p_, q_], x_) },
        rhs: {
            let exponent = &i_ * &p_ + &j_ * &q_;
            let multiplier = (&b__ * x_.pow(&i_)).pow(&p_)
                * (&c__ * x_.pow(&j_)).pow(&q_)
                / (&a__ * x_).pow(&exponent);
            rubi_star(multiplier, rubi_rhs_int(
                        &(u__ * (&a__ * x_).pow(&m_ + exponent)),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_30(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, i_, m_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 30,
        source: "Int[u_.*(a_.*x_)^m_.*(b_.*x_^i_.)^p_,x_Symbol] :=
          b^IntPart[p]*(b*x^i)^FracPart[p]/(a^(i*IntPart[p])*(a*x)^(i*FracPart[p])) \\[Star] Int[u*(a*x)^(m+i*p),x] /;
        FreeQ[{a,b,i,m,p},x] && IntegerQ[i] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u__, a__, m_, b__, i_, p_, x_],
        optional: [u__, a__, m_, b__, i_],
        when: {
            freeq!([a__, b__, i_, m_, p_], x_) && integerq!(i_) && !integerq!(p_)
        },
        rhs: {
            let int_p = rubi_int_part(&p_);
            let frac_p = rubi_frac_part(&p_);
            let multiplier = b__.pow(&int_p)
                * (&b__ * x_.pow(&i_)).pow(&frac_p)
                / (a__.pow(&i_ * &int_p) * (&a__ * x_).pow(&i_ * &frac_p));
            let exponent = rubi_simplify(&(&m_ + &i_ * &p_));
            let recursive_integrand = &u__ * (&a__ * x_).pow(exponent);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_31(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, i_, m_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 31,
        source: "Int[u_.*(a_.*x_)^m_.*(b_.*x_^i_.)^p_,x_Symbol] :=
          (b*x^i)^p/(a*x)^(i*p) \\[Star] Int[u*(a*x)^(m+i*p),x] /;
        FreeQ[{a,b,i,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u__, a__, m_, b__, i_, p_, x_],
        optional: [u__, a__, m_, b__, i_],
        when: { freeq!([a__, b__, i_, m_, p_], x_) && !integerq!(p_) },
        rhs: {
            let multiplier = (&b__ * x_.pow(&i_)).pow(&p_)
                / (&a__ * x_).pow(&i_ * &p_);
            let exponent = rubi_simplify(&(&m_ + &i_ * &p_));
            let recursive_integrand = &u__ * (&a__ * x_).pow(exponent);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_32(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, k_, m_, n_, p_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 32,
        source: "Int[u_.*(a_.*x_^m_)^p_.*(b_.*x_^n_)^q_.*(c_.*x_^k_)^r_.,x_Symbol] :=
          (a*x^m)^p*(b*x^n)^q*(c*x^k)^r/x^(m*p+n*q+k*r) \\[Star] Int[u*x^(m*p+n*q+k*r),x] /;
        FreeQ[{a,b,c,m,n,k,p,q,r},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (a__ * x_.pow(m_)).pow(p_)
            * (b__ * x_.pow(n_)).pow(q_)
            * (c__ * x_.pow(k_)).pow(r_),
        with: [u__, a__, m_, p_, b__, n_, q_, c__, k_, r_, x_],
        optional: [u__, a__, p_, b__, q_, c__, r_],
        x_free: [a__, b__, c__, m_, n_, k_, p_, q_, r_],
        when: { freeq!([a__, b__, c__, m_, n_, k_, p_, q_, r_], x_) },
        rhs: {
            let exponent = &m_ * &p_ + &n_ * &q_ + &k_ * &r_;
            let multiplier = (&a__ * x_.pow(&m_)).pow(&p_)
                * (&b__ * x_.pow(&n_)).pow(&q_)
                * (&c__ * x_.pow(&k_)).pow(&r_)
                / x_.pow(&exponent);
            rubi_star(multiplier, rubi_rhs_int(&(u__ * x_.pow(exponent)), x_))
        },
    ));
}

fn push_rules_rule_33(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 33,
        source: "Int[u_.*(a_.*x_^m_)^p_.*(b_.*x_^n_)^q_.,x_Symbol] :=
          a^IntPart[p]*b^IntPart[q]*(a*x^m)^FracPart[p]*(b*x^n)^FracPart[q]/x^(m*FracPart[p]+n*FracPart[q]) \\[Star] Int[u*x^(m*p+n*q),x] /;
        FreeQ[{a,b,m,n,p,q},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (a__ * x_.pow(m_)).pow(p_) * (b__ * x_.pow(n_)).pow(q_),
        with: [u__, a__, m_, p_, b__, n_, q_, x_],
        optional: [u__, a__, p_, b__, q_],
        x_free: [a__, b__, m_, n_, p_, q_],
        when: { freeq!([a__, b__, m_, n_, p_, q_], x_) },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let frac_q = rubi_frac_part(&q_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * b__.pow(rubi_int_part(&q_))
                * (&a__ * x_.pow(&m_)).pow(&frac_p)
                * (&b__ * x_.pow(&n_)).pow(&frac_q)
                / x_.pow(&m_ * frac_p + &n_ * frac_q);
            rubi_star(multiplier, rubi_rhs_int(&(u__ * x_.pow(&m_ * &p_ + &n_ * &q_)), x_))
        },
    ));
}

fn push_rules_rule_34(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 34,
        source: "Int[u_.*(a_.*x_^m_)^p_,x_Symbol] :=
          a^IntPart[p]*(a*x^m)^FracPart[p]/x^(m*FracPart[p]) \\[Star] Int[u*x^(m*p),x] /;
        FreeQ[{a,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (a__ * x_.pow(m_)).pow(p_),
        with: [u__, a__, m_, p_, x_],
        optional: [u__, a__],
        x_free: [a__, m_, p_],
        when: { freeq!([a__, m_, p_], x_) && !integerq!(p_) },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * (&a__ * x_.pow(&m_)).pow(&frac_p)
                / x_.pow(&m_ * &frac_p);
            rubi_star(multiplier, rubi_rhs_int(&(u__ * x_.pow(&m_ * &p_)), x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let i_ = symbols.i_;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ * x_).pow(m_) * (b__ * x_.pow(i_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ * x_.pow(n_)).pow(p_)
}
