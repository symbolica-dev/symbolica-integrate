use super::super::*;

fn push_rules_rule_215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 215,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          -x*(a+b*x^2)^(p+1)/(2*a*(p+1)) +
          (2*p+3)/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b},x] && LtQ[p,-1] && (IntegerQ[4*p] || IntegerQ[6*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).pow(p_),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && ltq!(p_, -1)
                && (integerq!(Atom::num(4) * &p_) || integerq!(Atom::num(6) * &p_))
        },
        rhs: {
            let p_plus_1 = &p_ + 1;
            let denominator = Atom::num(2) * &a__ * &p_plus_1;
            let base = &a__ + &b__ * x_.pow(2);
            let recursive = rubi_rhs_int(&base.pow(&p_plus_1), x_);
            let direct = Atom::num(-1) * x_ * base.pow(&p_plus_1) / &denominator;
            let multiplier = (Atom::num(2) * &p_ + 3) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, recursive)
        },
    ));
}

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_212(rules);
    push_rules_rule_213(rules);
    push_rules_rule_214(rules);
    push_rules_rule_215(rules);
    push_rules_rule_216(rules);
    push_rules_rule_217(rules);
    push_rules_rule_218(rules);
    push_rules_rule_219(rules);
    push_rules_rule_220(rules);
    push_rules_rule_221(rules);
    push_rules_rule_222(rules);
    push_rules_rule_223(rules);
    push_rules_rule_224(rules);
    push_rules_rule_225(rules);
    push_rules_rule_226(rules);
    push_rules_rule_227(rules);
    push_rules_rule_228(rules);
    push_rules_rule_229(rules);
    push_rules_rule_230(rules);
    push_rules_rule_231(rules);
    push_rules_rule_232(rules);
    push_rules_rule_746(rules);
    push_rules_rule_747(rules);
    push_rules_rule_748(rules);
    push_rules_rule_749(rules);
    push_rules_rule_750(rules);
    push_rules_rule_751(rules);
    push_rules_rule_752(rules);
    push_rules_rule_753(rules);
    push_rules_rule_754(rules);
    push_rules_rule_755(rules);
    push_rules_rule_756(rules);
    push_rules_rule_757(rules);
    push_rules_rule_758(rules);
    push_rules_rule_759(rules);
    push_rules_rule_760(rules);
    push_rules_rule_761(rules);
    push_rules_rule_762(rules);
    push_rules_rule_763(rules);
    push_rules_rule_764(rules);
    push_rules_rule_765(rules);
    push_rules_rule_766(rules);
    push_rules_rule_767(rules);
    push_rules_rule_768(rules);
    push_rules_rule_769(rules);
    push_rules_rule_770(rules);
    push_rules_rule_771(rules);
    push_rules_rule_772(rules);
    push_rules_rule_773(rules);
    push_rules_rule_774(rules);
    push_rules_rule_775(rules);
    push_rules_rule_776(rules);
    push_rules_rule_777(rules);
    push_rules_rule_778(rules);
    push_rules_rule_779(rules);
    push_rules_rule_239(rules);
    push_rules_rule_780(rules);
    push_rules_rule_781(rules);
    push_rules_rule_782(rules);
    push_rules_rule_783(rules);
    push_rules_rule_784(rules);
    push_rules_rule_785(rules);
    push_rules_rule_786(rules);
    push_rules_rule_787(rules);
    push_rules_rule_788(rules);
    push_rules_rule_789(rules);
    push_rules_rule_790(rules);
}

fn push_rules_rule_746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 746,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          x*(a+b*x^n)^(p+1)/a /;
        FreeQ[{a,b,n,p},x] && EqQ[1/n+p+1,0]",
        desc: "Binomial recurrence 3b with m\\[Equal]0 and 1n+p+1\\[Equal]0",
        refs: ["G&R 2.110.2, CRC 88d with n (p+1)+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && eqq!(Atom::num(1) / &n_ + &p_ + 1, 0)
        },
        rhs: {
            rubi_simp(&(x_ * (&a__ + &b__ * x_.pow(n_)).pow(&p_ + 1) / a__), x_)
        },
    ));
}

fn push_rules_rule_777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 777,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -x*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
          (n*(p+1)+1)/(a*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,n,p},x] && ILtQ[Simplify[1/n+p+1],0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let balance = rubi_simplify(&(Atom::num(1) / &n_ + &p_ + Atom::num(1)));
            freeq!([a__, b__, n_, p_], x_)
                && iltq!(balance, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let raised_p = &p_ + Atom::num(1);
            let denominator = &a__ * &n_ * &raised_p;
            let base = &a__ + &b__ * x_.pow(&n_);
            let recursive = rubi_rhs_int(&base.pow(&raised_p), x_);
            let coefficient = (&n_ * &raised_p + Atom::num(1)) / &denominator;
            rubi_simp(&(Atom::num(-1) * x_ * base.pow(raised_p) / &denominator), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 772,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Int[x^(n*p)*(b+a*x^(-n))^p,x] /;
        FreeQ[{a,b},x] && ILtQ[n,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && iltq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed_integrand =
                x_.pow(&n_ * &p_) * (&b__ + &a__ / x_.pow(&n_)).pow(&p_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 747,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(n_)).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 748,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          x*(a+b*x^n)^p/(n*p+1) +
          a*n*p/(n*p+1) \\[Star] Int[(a+b*x^n)^(p-1),x] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && GtQ[p,0] && (IntegerQ[2*p] || LtQ[Denominator[p+1/n],Denominator[p]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let shifted_denominator =
                rubi_denominator_atom(&(&p_ + Atom::num(1) / &n_));
            let p_denominator = rubi_denominator_atom(&p_);
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && (integerq!(Atom::num(2) * &p_)
                    || ltq!(shifted_denominator, p_denominator))
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let denominator = &n_ * &p_ + Atom::num(1);
            let recursive = rubi_rhs_int(&base.pow(&p_ - Atom::num(1)), x_);
            rubi_simp(&(x_ * base.pow(&p_) / &denominator), x_)
                    + rubi_star(&a__ * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 212,
        source: "Int[1/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
          2/(a^(5/4)*Rt[b/a,2])*EllipticE[1/2*ArcTan[Rt[b/a,2]*x],2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && PosQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(a__, 0)
                && posq!((&b__ / &a__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 2);
            let denominator = a__.pow((5, 4)) * &rt;
            rubi_simp(&(Atom::num(2) * rubi_elliptic_e((rt * x_).atan() / 2, Atom::num(2))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 213,
        source: "Int[1/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
          (1+b*x^2/a)^(1/4)/(a*(a+b*x^2)^(1/4)) \\[Star] Int[1/(1+b*x^2/a)^(5/4),x] /;
        FreeQ[{a,b},x] && PosQ[a] && PosQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && posq!(a__)
                && posq!((&b__ / &a__).expand())
        },
        rhs: {
            let normalized_base = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let base = &a__ + &b__ * x_.pow(2);
            let transformed_integrand = Atom::num(1) / normalized_base.pow((5, 4));
            let transformed = rubi_rhs_int(&transformed_integrand, x_);
            let multiplier = normalized_base.pow((1, 4)) / (&a__ * base.pow((1, 4)));
            rubi_star(multiplier, transformed)
        },
    ));
}

fn push_rules_rule_214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    let seven_sixths = Atom::num(7) / Atom::num(6);
    rules.push(rubi_rule!(
        order: 214,
        source: "Int[1/(a_+b_.*x_^2)^(7/6),x_Symbol] :=
          1/((a +b*x^2)^(2/3)*(a/(a+b*x^2))^(2/3)) \\[Star] Subst[Int[1/(1-b*x^2)^(1/3),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow(&seven_sixths),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                Atom::num(1) / (Atom::num(1) - &b__ * sub_atom.pow(2)).pow((1, 3));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let base = &a__ + &b__ * x_.pow(2);
            let scale = base.pow((2, 3)) * (&a__ / &base).pow((2, 3));
            let substituted = rubi_subst(&transformed, sub, x_ / base.sqrt());
            rubi_star(Atom::num(1) / scale, substituted)
        },
    ));
}

fn push_rules_rule_749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 749,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -x*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
          (n*(p+1)+1)/(a*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[p,-1] && (IntegerQ[2*p] || Denominator[p+1/n]<Denominator[p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let denominator_reduces =
                rational_denominator(&(&p_ + Atom::num(1) / &n_).expand())
                    .zip(rational_denominator(&p_))
                    .is_some_and(|(left, right)| left < right);
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && (integerq!(Atom::num(2) * &p_) || denominator_reduces)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let raised_p = &p_ + Atom::num(1);
            let denominator = &a__ * &n_ * &raised_p;
            let recursive = rubi_rhs_int(&base.pow(&raised_p), x_);
            let coefficient = (&n_ * &raised_p + Atom::num(1)) / &denominator;
            rubi_simp(&(Atom::num(-1) * x_ * base.pow(&raised_p) / &denominator), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 750,
        source: "Int[1/(a_+b_.*x_^3),x_Symbol] :=
          1/(3*Rt[a,3]^2) \\[Star] Int[1/(Rt[a,3]+Rt[b,3]*x),x] +
          1/(3*Rt[a,3]^2) \\[Star] Int[(2*Rt[a,3]-Rt[b,3]*x)/(Rt[a,3]^2-Rt[a,3]*Rt[b,3]*x+Rt[b,3]^2*x^2),x] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.126.1.2, CRC 74"],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(3)),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let rt_a = rubi_rt(&a__, 3);
            let rt_b = rubi_rt(&b__, 3);
            let coefficient = Atom::num(1) / (Atom::num(3) * rt_a.pow(2));
            let linear = rubi_rhs_int(&(Atom::num(1) / (&rt_a + &rt_b * x_)), x_);
            let quadratic_integrand = (Atom::num(2) * &rt_a - &rt_b * x_)
                / (rt_a.pow(2) - &rt_a * &rt_b * x_ + rt_b.pow(2) * x_.pow(2));
            let quadratic = rubi_rhs_int(&quadratic_integrand, x_);
            rubi_star(&coefficient, linear) + rubi_star(coefficient, quadratic)
        },
    ));
}

fn push_rules_rule_751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 751,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
          u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          r/(a*n) \\[Star] Int[1/(r+s*x),x] + 2*r/(a*n) \\[Star] Sum[u,{k,1,(n-1)/2}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-3)/2,0] && PosQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - 3) / 2, 0)
                && posq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ * &n_;
            let linear = rubi_rhs_int(&(Atom::num(1) / (&r + &s * x_)), x_);
            let mut sum = Atom::num(0);
            let pi = Atom::var(Symbol::PI);
            for k in 1..=((n_i64 - 1) / 2) {
                let cosine = (Atom::num(2 * k - 1) * &pi / &n_).cos();
                let integrand = (&r - &s * &cosine * x_)
                    / (r.pow(2) - Atom::num(2) * &r * &s * cosine * x_
                        + s.pow(2) * x_.pow(2));
                sum += rubi_rhs_int(&integrand, x_);
            }
            let linear_coefficient = &r / &denominator;
            let sum_coefficient = Atom::num(2) * &r / denominator;
            rubi_star(linear_coefficient, linear)
                    + rubi_star(sum_coefficient, sum)
        },
    ));
}

fn push_rules_rule_752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 752,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
          u=Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          r/(a*n) \\[Star] Int[1/(r-s*x),x] + 2*r/(a*n) \\[Star] Sum[u,{k,1,(n-1)/2}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-3)/2,0] && NegQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - 3) / 2, 0)
                && negq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(-&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ * &n_;
            let linear = rubi_rhs_int(&(Atom::num(1) / (&r - &s * x_)), x_);
            let mut sum = Atom::num(0);
            let pi = Atom::var(Symbol::PI);
            for k in 1..=((n_i64 - 1) / 2) {
                let cosine = (Atom::num(2 * k - 1) * &pi / &n_).cos();
                let integrand = (&r + &s * &cosine * x_)
                    / (r.pow(2) + Atom::num(2) * &r * &s * cosine * x_
                        + s.pow(2) * x_.pow(2));
                sum += rubi_rhs_int(&integrand, x_);
            }
            let linear_coefficient = &r / &denominator;
            let sum_coefficient = Atom::num(2) * &r / denominator;
            rubi_star(linear_coefficient, linear)
                    + rubi_star(sum_coefficient, sum)
        },
    ));
}

fn push_rules_rule_216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 216,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          1/(Rt[a,2]*Rt[b,2])*ArcTan[Rt[b,2]*x/Rt[a,2]] /;
        FreeQ[{a,b},x] && PosQ[a/b] && (GtQ[a,0] || GtQ[b,0])",
        desc: "Primitive rule",
        refs: ["G&R 2.124.1a, CRC 60, A&S 3.3.21"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && posq!((&a__ / &b__).expand())
                && (gtq!(a__, 0) || gtq!(b__, 0))
        },
        rhs: {
            let rt_a = rubi_rt(&a__, 2);
            let rt_b = rubi_rt(&b__, 2);
            let denominator = &rt_a * &rt_b;
            rubi_simp(&((&rt_b * x_ / rt_a).atan() / denominator), x_)
        },
    ));
}

fn push_rules_rule_217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 217,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          -1/(Rt[-a,2]*Rt[-b,2])*ArcTan[Rt[-b,2]*x/Rt[-a,2]] /;
        FreeQ[{a,b},x] && PosQ[a/b] && (LtQ[a,0] || LtQ[b,0])",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && posq!((&a__ / &b__).expand())
                && (ltq!(a__, 0) || ltq!(b__, 0))
        },
        rhs: {
            let rt_neg_a = rubi_rt(&(-&a__), 2);
            let rt_neg_b = rubi_rt(&(-&b__), 2);
            let denominator = &rt_neg_a * &rt_neg_b;
            rubi_simp(&(-(&rt_neg_b * x_ / rt_neg_a).atan() / denominator), x_)
        },
    ));
}

fn push_rules_rule_218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 218,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          Rt[a/b,2]/a*ArcTan[x/Rt[a/b,2]] /;
        FreeQ[{a,b},x] && PosQ[a/b]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_) && posq!((&a__ / &b__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(&a__ / &b__), 2);
            rubi_simp(&(&rt * (x_ / &rt).atan() / a__), x_)
        },
    ));
}

fn push_rules_rule_219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 219,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          1/(Rt[a,2]*Rt[-b,2])*ArcTanh[Rt[-b,2]*x/Rt[a,2]] /;
        FreeQ[{a,b},x] && NegQ[a/b] && (GtQ[a,0] || LtQ[b,0])",
        desc: "Primitive rule",
        refs: ["G&R 2.124.1b', CRC 61b, A&S 3.3.23"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && negq!((&a__ / &b__).expand())
                && (gtq!(a__, 0) || ltq!(b__, 0))
        },
        rhs: {
            let rt_a = rubi_rt(&a__, 2);
            let rt_neg_b = rubi_rt(&(-&b__), 2);
            let denominator = &rt_a * &rt_neg_b;
            rubi_simp(&((&rt_neg_b * x_ / rt_a).atanh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 220,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          -1/(Rt[-a,2]*Rt[b,2])*ArcTanh[Rt[b,2]*x/Rt[-a,2]] /;
        FreeQ[{a,b},x] && NegQ[a/b] && (LtQ[a,0] || GtQ[b,0])",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && negq!((&a__ / &b__).expand())
                && (ltq!(a__, 0) || gtq!(b__, 0))
        },
        rhs: {
            let rt_neg_a = rubi_rt(&(-&a__), 2);
            let rt_b = rubi_rt(&b__, 2);
            let denominator = &rt_neg_a * &rt_b;
            rubi_simp(&(-(&rt_b * x_ / rt_neg_a).atanh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 221,
        source: "Int[1/(a_+b_.*x_^2),x_Symbol] :=
          Rt[-a/b,2]/a*ArcTanh[x/Rt[-a/b,2]] /;
        FreeQ[{a,b},x] && NegQ[a/b]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_) && negq!((&a__ / &b__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 2);
            rubi_simp(&(&rt * (x_ / &rt).atanh() / a__), x_)
        },
    ));
}

fn push_rules_rule_753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 753,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u, v},
          u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] +
            Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          2*r^2/(a*n) \\[Star] Int[1/(r^2+s^2*x^2),x] + 2*r/(a*n) \\[Star] Sum[u,{k,1,(n-2)/4}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && PosQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - 2) / 4, 0)
                && posq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let r2 = r.pow(2);
            let denominator = &a__ * &n_;
            let base = rubi_rhs_int(
                &(Atom::num(1) / (&r2 + s.pow(2) * x_.pow(2))),
                x_,
            );
            let mut sum = Atom::num(0);
            let pi = Atom::var(Symbol::PI);
            for k in 1..=((n_i64 - 2) / 4) {
                let cosine = (Atom::num(2 * k - 1) * &pi / &n_).cos();
                let first = (&r - &s * &cosine * x_)
                    / (&r2 - Atom::num(2) * &r * &s * &cosine * x_
                        + s.pow(2) * x_.pow(2));
                let second = (&r + &s * &cosine * x_)
                    / (&r2 + Atom::num(2) * &r * &s * cosine * x_
                        + s.pow(2) * x_.pow(2));
                sum += rubi_rhs_int(&first, x_) + rubi_rhs_int(&second, x_);
            }
            let base_coefficient = Atom::num(2) * &r2 / &denominator;
            let sum_coefficient = Atom::num(2) * &r / denominator;
            rubi_star(base_coefficient, base)
                    + rubi_star(sum_coefficient, sum)
        },
    ));
}

fn push_rules_rule_754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 754,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
          u=Int[(r-s*Cos[(2*k*Pi)/n]*x)/(r^2-2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x] +
            Int[(r+s*Cos[(2*k*Pi)/n]*x)/(r^2+2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x];
          2*r^2/(a*n) \\[Star] Int[1/(r^2-s^2*x^2),x] + 2*r/(a*n) \\[Star] Sum[u,{k,1,(n-2)/4}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && NegQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - 2) / 4, 0)
                && negq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(-&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let r2 = r.pow(2);
            let denominator = &a__ * &n_;
            let base = rubi_rhs_int(
                &(Atom::num(1) / (&r2 - s.pow(2) * x_.pow(2))),
                x_,
            );
            let mut sum = Atom::num(0);
            let pi = Atom::var(Symbol::PI);
            for k in 1..=((n_i64 - 2) / 4) {
                let cosine = (Atom::num(2 * k) * &pi / &n_).cos();
                let first = (&r - &s * &cosine * x_)
                    / (&r2 - Atom::num(2) * &r * &s * &cosine * x_
                        + s.pow(2) * x_.pow(2));
                let second = (&r + &s * &cosine * x_)
                    / (&r2 + Atom::num(2) * &r * &s * cosine * x_
                        + s.pow(2) * x_.pow(2));
                sum += rubi_rhs_int(&first, x_) + rubi_rhs_int(&second, x_);
            }
            let base_coefficient = Atom::num(2) * &r2 / &denominator;
            let sum_coefficient = Atom::num(2) * &r / denominator;
            rubi_star(base_coefficient, base)
                    + rubi_star(sum_coefficient, sum)
        },
    ));
}

fn push_rules_rule_755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 755,
        source: "Int[1/(a_+b_.*x_^4),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
          1/(2*r) \\[Star] Int[(r-s*x^2)/(a+b*x^4),x] + 1/(2*r) \\[Star] Int[(r+s*x^2)/(a+b*x^4),x]] /;
        FreeQ[{a,b},x] && (GtQ[a/b,0] || PosQ[a/b] && AtomQ[SplitProduct[SumBaseQ,a]] && AtomQ[SplitProduct[SumBaseQ,b]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: {
            let ratio = (&a__ / &b__).expand();
            freeq!([a__, b__], x_)
                && (gtq!(ratio, 0)
                    || posq!(ratio)
                        && rubi_atomq_split_product_sum_base(&a__)
                        && rubi_atomq_split_product_sum_base(&b__))
        },
        rhs: {
            let root = rubi_rt(&(&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ + &b__ * x_.pow(4);
            let first = rubi_rhs_int(&((&r - &s * x_.pow(2)) / &denominator), x_);
            let second = rubi_rhs_int(&((&r + &s * x_.pow(2)) / denominator), x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * r);
            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 756,
        source: "Int[1/(a_+b_.*x_^4),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          r/(2*a) \\[Star] Int[1/(r-s*x^2),x] + r/(2*a) \\[Star] Int[1/(r+s*x^2),x]] /;
        FreeQ[{a,b},x] && Not[GtQ[a/b,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && !gtq!((&a__ / &b__).expand(), 0) },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let first = rubi_rhs_int(&(Atom::num(1) / (&r - &s * x_.pow(2))), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (&r + &s * x_.pow(2))), x_);
            let coefficient = &r / (Atom::num(2) * &a__);
            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 757,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
          r/(2*Sqrt[2]*a) \\[Star] Int[(Sqrt[2]*r-s*x^(n/4))/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] +
          r/(2*Sqrt[2]*a) \\[Star] Int[(Sqrt[2]*r+s*x^(n/4))/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
        FreeQ[{a,b},x] && IGtQ[n/4,1] && GtQ[a/b,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.132.1.1', CRC 77'"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(&n_ / 4, 1)
                && gtq!((&a__ / &b__).expand(), 0)
        },
        rhs: {
            let root = rubi_rt(&(&a__ / &b__), 4);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let sqrt_two = Atom::num(2).sqrt();
            let n_over_4 = &n_ / 4;
            let n_over_2 = &n_ / 2;
            let x_n_over_4 = x_.pow(&n_over_4);
            let first_integrand = (&sqrt_two * &r - &s * &x_n_over_4)
                / (r.pow(2) - &sqrt_two * &r * &s * &x_n_over_4
                    + s.pow(2) * x_.pow(&n_over_2));
            let second_integrand = (&sqrt_two * &r + &s * &x_n_over_4)
                / (r.pow(2) + &sqrt_two * &r * &s * &x_n_over_4
                    + s.pow(2) * x_.pow(n_over_2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &r / (Atom::num(2) * &sqrt_two * &a__);
            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 758,
        source: "Int[1/(a_+b_.*x_^n_),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          r/(2*a) \\[Star] Int[1/(r-s*x^(n/2)),x] + r/(2*a) \\[Star] Int[1/(r+s*x^(n/2)),x]] /;
        FreeQ[{a,b},x] && IGtQ[n/4,1] && Not[GtQ[a/b,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(&n_ / 4, 1)
                && !gtq!((&a__ / &b__).expand(), 0)
        },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let x_n_over_2 = x_.pow(&n_ / 2);
            let first = rubi_rhs_int(&(Atom::num(1) / (&r - &s * &x_n_over_2)), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (&r + &s * &x_n_over_2)), x_);
            let coefficient = &r / (Atom::num(2) * &a__);
            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 222,
        source: "Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          ArcSinh[Rt[b,2]*x/Sqrt[a]]/Rt[b,2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && PosQ[b]",
        desc: "Primitive rule",
        refs: ["CRC 278"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && gtq!(a__, 0) && posq!(b__) },
        rhs: {
            let rt_b = rubi_rt(&b__, 2);
            rubi_simp(&((&rt_b * x_ / a__.sqrt()).asinh() / rt_b), x_)
        },
    ));
}

fn push_rules_rule_223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 223,
        source: "Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          ArcSin[Rt[-b,2]*x/Sqrt[a]]/Rt[-b,2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && NegQ[b]",
        desc: "Primitive rule",
        refs: ["G&R 2.271.4b, CRC 279, A&S 3.3.44"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && gtq!(a__, 0) && negq!(b__) },
        rhs: {
            let rt_neg_b = rubi_rt(&(-b__), 2);
            rubi_simp(&((&rt_neg_b * x_ / a__.sqrt()).asin() / rt_neg_b), x_)
        },
    ));
}

fn push_rules_rule_224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 224,
        source: "Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          Subst[Int[1/(1-b*x^2),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b},x] && Not[GtQ[a,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && !gtq!(a__, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) - &b__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = x_ / (a__ + b__ * x_.pow(2)).sqrt();

            rubi_subst(&transformed, sub, replacement)
        },
    ));
}

fn push_rules_rule_759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 759,
        source: "Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          2*Sqrt[2+Sqrt[3]]*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1+Sqrt[3])*s+r*x)^2]/
            (3^(1/4)*r*Sqrt[a+b*x^3]*Sqrt[s*(s+r*x)/((1+Sqrt[3])*s+r*x)^2])*
            EllipticF[ArcSin[((1-Sqrt[3])*s+r*x)/((1+Sqrt[3])*s+r*x)],-7-4*Sqrt[3]]] /;
        FreeQ[{a,b},x] && PosQ[a]",
        desc: "Piecewise constant extraction, integration by the M\\[ODoubleDot]bius substitution, and piecewise constant extraction",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!(a__) },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let sqrt_three = Atom::num(3).sqrt();
            let denominator_linear = (Atom::num(1) + &sqrt_three) * &s + &r * x_;
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_ + r.pow(2) * x_.pow(2))
                    / denominator_linear.pow(2);
            let radical_linear = &s * (&s + &r * x_) / denominator_linear.pow(2);
            let amplitude =
                (((Atom::num(1) - &sqrt_three) * &s + &r * x_) / denominator_linear).asin();

            rubi_simp(&(Atom::num(2)
                    * (Atom::num(2) + &sqrt_three).sqrt()
                    * (&s + &r * x_)
                    * radical_quadratic.sqrt()
                    * rubi_elliptic_f(amplitude, -Atom::num(7) - Atom::num(4) * sqrt_three)
                    / (Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * r
                        * (&a__ + &b__ * x_.pow(3)).sqrt()
                        * radical_linear.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_760(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 760,
        source: "Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          2*Sqrt[2-Sqrt[3]]*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1-Sqrt[3])*s+r*x)^2]/
            (3^(1/4)*r*Sqrt[a+b*x^3]*Sqrt[-s*(s+r*x)/((1-Sqrt[3])*s+r*x)^2])*
            EllipticF[ArcSin[((1+Sqrt[3])*s+r*x)/((1-Sqrt[3])*s+r*x)],-7+4*Sqrt[3]]] /;
        FreeQ[{a,b},x] && NegQ[a]",
        desc: "Piecewise constant extraction, integration by the M\\[ODoubleDot]bius substitution, and piecewise constant extraction",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!(a__) },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let sqrt_three = Atom::num(3).sqrt();
            let denominator_linear = (Atom::num(1) - &sqrt_three) * &s + &r * x_;
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_ + r.pow(2) * x_.pow(2))
                    / denominator_linear.pow(2);
            let radical_linear = -&s * (&s + &r * x_) / denominator_linear.pow(2);
            let amplitude =
                (((Atom::num(1) + &sqrt_three) * &s + &r * x_) / denominator_linear).asin();

            rubi_simp(&(Atom::num(2)
                    * (Atom::num(2) - &sqrt_three).sqrt()
                    * (&s + &r * x_)
                    * radical_quadratic.sqrt()
                    * rubi_elliptic_f(amplitude, -Atom::num(7) + Atom::num(4) * sqrt_three)
                    / (Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * r
                        * (&a__ + &b__ * x_.pow(3)).sqrt()
                        * radical_linear.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_761(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 761,
        source: "Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[b/a,4]},
          (1+q^2*x^2)*Sqrt[(a+b*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^4])*EllipticF[2*ArcTan[q*x],1/2]] /;
        FreeQ[{a,b},x] && PosQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: ["G&R 3.166.1"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!((&b__ / &a__).expand()) },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 4);
            let one_plus = Atom::num(1) + q.pow(2) * x_.pow(2);
            rubi_simp(&(&one_plus
                    * ((&a__ + &b__ * x_.pow(4)) / (&a__ * one_plus.pow(2))).sqrt()
                    * rubi_elliptic_f(Atom::num(2) * (&q * x_).atan(), Atom::num(1) / 2)
                    / (Atom::num(2) * q * (a__ + b__ * x_.pow(4)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 762,
        source: "Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          1/(Sqrt[a]*Rt[-b/a,4])*EllipticF[ArcSin[Rt[-b/a,4]*x],-1] /;
        FreeQ[{a,b},x] && NegQ[b/a] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) && gtq!(a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 4);
            rubi_simp(&(rubi_elliptic_f((&q * x_).asin(), -Atom::num(1))
                    / (a__.sqrt() * q)), x_)
        },
    ));
}

fn push_rules_rule_763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 763,
        source: "Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*b,2]},
          Sqrt[-a+q*x^2]*Sqrt[(a+q*x^2)/q]/(Sqrt[2]*Sqrt[-a]*Sqrt[a+b*x^4])*
            EllipticF[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
          IntegerQ[q]] /;
        FreeQ[{a,b},x] && LtQ[a,0] && GtQ[b,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.3+"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: {
            let q = rubi_rt(&(-&a__ * &b__), 2);
            freeq!([a__, b__], x_) && ltq!(a__, 0) && gtq!(b__, 0) && integerq!(q)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &b__), 2);
            let amplitude = (x_ / ((&a__ + &q * x_.pow(2)) / (Atom::num(2) * &q)).sqrt()).asin();
            (-&a__ + &q * x_.pow(2)).sqrt()
                    * ((&a__ + &q * x_.pow(2)) / &q).sqrt()
                    * rubi_elliptic_f(amplitude, Atom::num(1) / 2)
                    / (Atom::num(2).sqrt()
                        * (-&a__).sqrt()
                        * (a__ + b__ * x_.pow(4)).sqrt())
        },
    ));
}

fn push_rules_rule_764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 764,
        source: "Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[-a*b,2]},
          Sqrt[(a-q*x^2)/(a+q*x^2)]*Sqrt[(a+q*x^2)/q]/(Sqrt[2]*Sqrt[a+b*x^4]*Sqrt[a/(a+q*x^2)])*
            EllipticF[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2]] /;
        FreeQ[{a,b},x] && LtQ[a,0] && GtQ[b,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.3+"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && ltq!(a__, 0) && gtq!(b__, 0) },
        rhs: {
            let q = rubi_rt(&(-&a__ * &b__), 2);
            let a_plus_qx2 = &a__ + &q * x_.pow(2);
            let amplitude = (x_ / ((&a_plus_qx2) / (Atom::num(2) * &q)).sqrt()).asin();
            rubi_simp(&(((&a__ - &q * x_.pow(2)) / &a_plus_qx2).sqrt()
                    * (&a_plus_qx2 / &q).sqrt()
                    * rubi_elliptic_f(amplitude, Atom::num(1) / 2)
                    / (Atom::num(2).sqrt()
                        * (&a__ + &b__ * x_.pow(4)).sqrt()
                        * (&a__ / a_plus_qx2).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 765,
        source: "Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          Sqrt[1+b*x^4/a]/Sqrt[a+b*x^4] \\[Star] Int[1/Sqrt[1+b*x^4/a],x] /;
        FreeQ[{a,b},x] && NegQ[b/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) && !gtq!(a__, 0)
        },
        rhs: {
            let recursive_integrand = Atom::num(1) / (Atom::num(1) + &b__ * x_.pow(4) / &a__).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (Atom::num(1) + &b__ * x_.pow(4) / &a__).sqrt()
                / (a__ + b__ * x_.pow(4)).sqrt();
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 766,
        source: "Int[1/Sqrt[a_+b_.*x_^6],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
            (2*3^(1/4)*s*Sqrt[a+b*x^6]*Sqrt[r*x^2*(s+r*x^2)/(s+(1+Sqrt[3])*r*x^2)^2])*
            EllipticF[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4]] /;
        FreeQ[{a,b},x]",
        desc: "Piecewise constant extraction and integration by the substitution",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(6)).sqrt(),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let root = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let sqrt_three = Atom::num(3).sqrt();
            let denominator_linear = &s + (Atom::num(1) + &sqrt_three) * &r * x_.pow(2);
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_.pow(2) + r.pow(2) * x_.pow(4))
                    / denominator_linear.pow(2);
            let radical_linear =
                &r * x_.pow(2) * (&s + &r * x_.pow(2)) / denominator_linear.pow(2);
            let amplitude =
                ((&s + (Atom::num(1) - &sqrt_three) * &r * x_.pow(2)) / denominator_linear)
                    .acos();

            rubi_simp(&(x_
                    * (&s + &r * x_.pow(2))
                    * radical_quadratic.sqrt()
                    * rubi_elliptic_f(amplitude, (Atom::num(2) + sqrt_three) / 4)
                    / (Atom::num(2)
                        * Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * s
                        * (&a__ + &b__ * x_.pow(6)).sqrt()
                        * radical_linear.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 767,
        source: "Int[1/Sqrt[a_+b_.*x_^8],x_Symbol] :=
          1/2 \\[Star] Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] +
          1/2 \\[Star] Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(8)).sqrt(),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 4);
            let base = (&a__ + &b__ * x_.pow(8)).sqrt();
            let first = rubi_rhs_int(&((Atom::num(1) - &q * x_.pow(2)) / &base), x_);
            let second = rubi_rhs_int(&((Atom::num(1) + &q * x_.pow(2)) / base), x_);
            let half = Atom::num(1) / 2;
            rubi_star(&half, first) + rubi_star(half, second)
        },
    ));
}

fn push_rules_rule_768(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 768,
        source: "Int[1/(a_+b_.*x_^4)^(3/4),x_Symbol] :=
          x^3*(1+a/(b*x^4))^(3/4)/(a+b*x^4)^(3/4) \\[Star] Int[1/(x^3*(1+a/(b*x^4))^(3/4)),x] /;
        FreeQ[{a,b},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(4)).pow((3, 4)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let normalized = Atom::num(1) + &a__ / (&b__ * x_.pow(4));
            let recursive = rubi_rhs_int(
                &(Atom::num(1) / (x_.pow(3) * normalized.pow((3, 4)))),
                x_,
            );
            let multiplier = x_.pow(3) * normalized.pow((3, 4))
                / (&a__ + &b__ * x_.pow(4)).pow((3, 4));
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 225,
        source: "Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          2*x/(a+b*x^2)^(1/4) - a \\[Star] Int[1/(a+b*x^2)^(5/4),x] /;
        FreeQ[{a,b},x] && GtQ[a,0] && PosQ[b/a]",
        desc: "Binomial recurrence 1b",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(a__, 0)
                && posq!((&b__ / &a__).expand())
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / base.pow((5, 4))), x_);

            rubi_simp(&(Atom::num(2) * x_ / base.pow((1, 4))), x_)
                    - rubi_star(a__, recursive)
        },
    ));
}

fn push_rules_rule_226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 226,
        source: "Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          2/(a^(1/4)*Rt[-b/a,2])*EllipticE[1/2*ArcSin[Rt[-b/a,2]*x],2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && NegQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(a__, 0)
                && negq!((&b__ / &a__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ / &a__), 2);
            let denominator = a__.pow((1, 4)) * &rt;
            rubi_simp(&(Atom::num(2)
                    * rubi_elliptic_e((rt * x_).asin() / 2, Atom::num(2))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 227,
        source: "Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          (1+b*x^2/a)^(1/4)/(a+b*x^2)^(1/4) \\[Star] Int[1/(1+b*x^2/a)^(1/4),x] /;
        FreeQ[{a,b},x] && PosQ[a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && posq!(a__) },
        rhs: {
            let normalized_base = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let base = &a__ + &b__ * x_.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / normalized_base.pow((1, 4))), x_);
            let multiplier = normalized_base.pow((1, 4)) / base.pow((1, 4));
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 228,
        source: "Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
          2*Sqrt[-b*x^2/a]/(b*x) \\[Star] Subst[Int[x^2/Sqrt[1-x^4/a],x],x,(a+b*x^2)^(1/4)] /;
        FreeQ[{a,b},x] && NegQ[a]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && negq!(a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow(2) / (Atom::num(1) - sub_atom.pow(4) / &a__).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&a__ + &b__ * x_.pow(2)).pow((1, 4));
            let multiplier = Atom::num(2) * (-&b__ * x_.pow(2) / &a__).sqrt()
                / (b__ * x_);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 229,
        source: "Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
          2/(a^(3/4)*Rt[b/a,2])*EllipticF[1/2*ArcTan[Rt[b/a,2]*x],2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && PosQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(a__, 0)
                && posq!((&b__ / &a__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 2);
            let denominator = a__.pow((3, 4)) * &rt;
            rubi_simp(&(Atom::num(2)
                    * rubi_elliptic_f((rt * x_).atan() / 2, Atom::num(2))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 230,
        source: "Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
          2/(a^(3/4)*Rt[-b/a,2])*EllipticF[1/2*ArcSin[Rt[-b/a,2]*x],2] /;
        FreeQ[{a,b},x] && GtQ[a,0] && NegQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(a__, 0)
                && negq!((&b__ / &a__).expand())
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ / &a__), 2);
            let denominator = a__.pow((3, 4)) * &rt;
            rubi_simp(&(Atom::num(2)
                    * rubi_elliptic_f((rt * x_).asin() / 2, Atom::num(2))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 231,
        source: "Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
          (1+b*x^2/a)^(3/4)/(a+b*x^2)^(3/4) \\[Star] Int[1/(1+b*x^2/a)^(3/4),x] /;
        FreeQ[{a,b},x] && PosQ[a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && posq!(a__) },
        rhs: {
            let normalized_base = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let base = &a__ + &b__ * x_.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / normalized_base.pow((3, 4))), x_);
            let multiplier = normalized_base.pow((3, 4)) / base.pow((3, 4));
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 232,
        source: "Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
          2*Sqrt[-b*x^2/a]/(b*x) \\[Star] Subst[Int[1/Sqrt[1-x^4/a],x],x,(a+b*x^2)^(1/4)] /;
        FreeQ[{a,b},x] && NegQ[a]",
        desc: "Piecewise constant extranction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && negq!(a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                Atom::num(1) / (Atom::num(1) - sub_atom.pow(4) / &a__).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&a__ + &b__ * x_.pow(2)).pow((1, 4));
            let multiplier = Atom::num(2) * (-&b__ * x_.pow(2) / &a__).sqrt()
                / (b__ * x_);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_769(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 769,
        source: "Int[1/(a_+b_.*x_^3)^(1/3),x_Symbol] :=
          ArcTan[(1+2*Rt[b,3]*x/(a+b*x^3)^(1/3))/Sqrt[3]]/(Sqrt[3]*Rt[b,3]) - Log[(a+b*x^3)^(1/3)-Rt[b,3]*x]/(2*Rt[b,3]) /;
        FreeQ[{a,b},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(3)).pow((1, 3)),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let rt_b = rubi_rt(&b__, 3);
            let base_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let sqrt_three = Atom::num(3).sqrt();
            rubi_simp(&(((Atom::num(1) + Atom::num(2) * &rt_b * x_ / &base_root) / &sqrt_three)
                    .atan()
                    / (&sqrt_three * &rt_b)), x_)
                    - rubi_simp(&((base_root - &rt_b * x_).log() / (Atom::num(2) * rt_b)), x_)
        },
    ));
}

fn push_rules_rule_770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 770,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^(p+1/n) \\[Star] Subst[Int[1/(1-b*x^n)^(p+1/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegerQ[p+1/n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let exponent_sum = &p_ + Atom::num(1) / &n_;
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && integerq!(exponent_sum)
        },
        rhs: {
            let exponent_sum = &p_ + Atom::num(1) / &n_;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / (Atom::num(1) - &b__ * sub_atom.pow(&n_))
                    .pow(&exponent_sum + Atom::num(1));
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let base = &a__ + &b__ * x_.pow(&n_);
            let replacement = x_ / base.pow(Atom::num(1) / &n_);
            let substituted = rubi_subst(&primitive, sub, replacement);
            rubi_star(a__.pow(exponent_sum), substituted)
        },
    ));
}

fn push_rules_rule_771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 771,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (a/(a+b*x^n))^(p+1/n)*(a+b*x^n)^(p+1/n) \\[Star] Subst[Int[1/(1-b*x^n)^(p+1/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] && LtQ[Denominator[p+1/n],Denominator[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let shifted = &p_ + Atom::num(1) / &n_;
            let shifted_denominator = rubi_denominator_atom(&shifted);
            let p_denominator = rubi_denominator_atom(&p_);
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && ltq!(shifted_denominator, p_denominator)
        },
        rhs: {
            let shifted = &p_ + Atom::num(1) / &n_;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / (Atom::num(1) - &b__ * sub_atom.pow(&n_)).pow(&shifted + Atom::num(1));
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let base = &a__ + &b__ * x_.pow(&n_);
            let substituted = rubi_subst(
                &primitive,
                sub,
                x_ / base.pow(Atom::num(1) / &n_),
            );
            let multiplier = (&a__ / &base).pow(&shifted) * base.pow(shifted);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 773,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,p},x] && ILtQ[n,0] && Not[IntegerQ[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_) && iltq!(n_, 0) && !integerq!(p_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ / sub_atom.pow(&n_)).pow(&p_) / sub_atom.pow(2);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            -rubi_subst(
                &primitive,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 774,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*x^(k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,p},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: { freeq!([a__, b__, p_], x_) && fractionq!(n_) },
        rhs: {
            let denominator = rubi_denominator(&n_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let k = Atom::num(denominator);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                x_.pow(Atom::num(1) / &k),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 775,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: { freeq!([a__, b__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 776,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          x*(a+b*x^n)^p*(x^n/(a+b*x^n))^p/n \\[Star] Subst[Int[1/(x^(p+1)*(1-b*x)),x],x,x^n/(a+b*x^n)] /;
        FreeQ[{a,b,n,p},x] && EqQ[1/n+p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && eqq!(Atom::num(1) / &n_ + &p_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / (sub_atom.pow(&p_ + Atom::num(1))
                    * (Atom::num(1) - &b__ * &sub_atom));
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let base = &a__ + &b__ * x_.pow(&n_);
            let replacement = x_.pow(&n_) / &base;
            let substituted = rubi_subst(&primitive, sub, &replacement);
            let multiplier = x_ * base.pow(&p_) * replacement.pow(&p_) / &n_;
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 778,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^p*x*Hypergeometric2F1[-p,1/n,1/n+1,-b*x^n/a] /;
        FreeQ[{a,b,n,p},x] && Not[IGtQ[p,0]] && Not[IntegerQ[1/n]] && Not[ILtQ[Simplify[1/n+p],0]] &&
          (IntegerQ[p] || GtQ[a,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let shifted = (Atom::num(1) / &n_ + &p_).expand();
            freeq!([a__, b__, n_, p_], x_)
                && !igtq!(p_, 0)
                && !integerq!(Atom::num(1) / &n_)
                && !iltq!(shifted, 0)
                && (integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let one_over_n = Atom::num(1) / &n_;
            rubi_simp(
                &(a__.pow(&p_)
                    * x_
                    * rubi_hypergeometric2f1(
                        -&p_,
                        &one_over_n,
                        &one_over_n + Atom::num(1),
                        -&b__ * x_.pow(&n_) / a__,
                    )),
                x_,
            )
        },
    ));
}

fn push_rules_rule_779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 779,
        source: "Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p] \\[Star] Int[(1+b*x^n/a)^p,x] /;
        FreeQ[{a,b,n,p},x] && Not[IGtQ[p,0]] && Not[IntegerQ[1/n]] &&
          Not[ILtQ[Simplify[1/n+p],0]] && Not[IntegerQ[p] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            let shifted = (Atom::num(1) / &n_ + &p_).expand();
            freeq!([a__, b__, n_, p_], x_)
                && !igtq!(p_, 0)
                && !integerq!(Atom::num(1) / &n_)
                && !iltq!(shifted, 0)
                && !(integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let normalized_base = Atom::num(1) + &b__ * x_.pow(&n_) / &a__;
            let recursive = rubi_rhs_int(&normalized_base.pow(&p_), x_);
            rubi_star(a__.pow(rubi_int_part(&p_)) * (a__ + b__ * x_.pow(&n_)).pow(rubi_frac_part(&p_)) / normalized_base.pow(rubi_frac_part(&p_)), recursive)
        },
    ));
}

fn push_rules_rule_239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, v__);
    rules.push(rubi_rule!(
        order: 239,
        source: "Int[(a_.+b_.*v_^n_)^p_,x_Symbol] :=
          1/Coefficient[v,x,1] \\[Star] Subst[Int[(a+b*x^n)^p,x],x,v] /;
        FreeQ[{a,b,n,p},x] && LinearQ[v,x] && NeQ[v,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * v__.pow(n_)).pow(p_),
        with: [a__, b__, v__, n_, p_, x_],
        optional: [a__, b__],
        x_dep: [],
        x_free: [a__, b__, n_, p_],
        x_linear: [v__],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && rubi_linear_q(&v__, x_)
                && neq!(v__, x_)
        },
        rhs: {
            let slope = rubi_coefficient(&v__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, v__);
            rubi_star(Atom::num(1) / slope, substituted)
        },
    ));
}

fn push_rules_rule_780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 780,
        source: "Int[(a1_.+b1_.*x_^n_)^p_.*(a2_.+b2_.*x_^n_)^p_.,x_Symbol] :=
          Int[(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,n,p},x] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [a1__, b1__, a2__, b2__, p_],
        x_free: [a1__, b1__, a2__, b2__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let transformed_integrand =
                (&a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 781,
        source: "Int[(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
          x*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(2*n*p+1) +
          2*a1*a2*n*p/(2*n*p+1) \\[Star] Int[(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
        FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && GtQ[p,0] && (IntegerQ[2*p] || Denominator[p+1/n]<Denominator[p])",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__, n_, p_],
        x_free: [a1__, b1__, a2__, b2__, n_, p_],
        when: {
            let denominator_condition =
                rational_denominator(&(&p_ + Atom::num(1) / &n_).expand())
                    .zip(rational_denominator(&p_))
                    .map(|(left, right)| left < right)
                    .unwrap_or(false);
            freeq!([a1__, b1__, a2__, b2__], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!((Atom::num(2) * &n_).expand(), 0)
                && gtq!(p_, 0)
                && (integerq!(Atom::num(2) * &p_) || denominator_condition)
        },
        rhs: {
            let denominator = Atom::num(2) * &n_ * &p_ + Atom::num(1);
            let lhs = &a1__ + &b1__ * x_.pow(&n_);
            let rhs = &a2__ + &b2__ * x_.pow(&n_);
            let lowered = &p_ - Atom::num(1);
            let recursive_integrand = lhs.pow(&lowered) * rhs.pow(&lowered);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(2) * &a1__ * &a2__ * &n_ * &p_ / &denominator;

            rubi_simp(&(x_ * lhs.pow(&p_) * rhs.pow(&p_) / &denominator), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 782,
        source: "Int[(a1_+b1_.*x_^n_.)^p_*(a2_+b2_.*x_^n_.)^p_,x_Symbol] :=
          -x*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*n*(p+1)) +
          (2*n*(p+1)+1)/(2*a1*a2*n*(p+1)) \\[Star] Int[(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[p,-1] && (IntegerQ[2*p] || Denominator[p+1/n]<Denominator[p])",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__, n_],
        when: {
            let denominator_condition =
                rational_denominator(&(&p_ + Atom::num(1) / &n_).expand())
                    .zip(rational_denominator(&p_))
                    .map(|(left, right)| left < right)
                    .unwrap_or(false);
            freeq!([a1__, b1__, a2__, b2__], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!((Atom::num(2) * &n_).expand(), 0)
                && ltq!(p_, -1)
                && (integerq!(Atom::num(2) * &p_) || denominator_condition)
        },
        rhs: {
            let raised = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * &a1__ * &a2__ * &n_ * &raised;
            let lhs = &a1__ + &b1__ * x_.pow(&n_);
            let rhs = &a2__ + &b2__ * x_.pow(&n_);
            let recursive_integrand = lhs.pow(&raised) * rhs.pow(&raised);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_coefficient =
                (Atom::num(2) * &n_ * &raised + Atom::num(1)) / &denominator;

            rubi_simp(&(Atom::num(-1) * x_ * lhs.pow(&raised) * rhs.pow(raised) / &denominator), x_)
                    + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 783,
        source: "Int[(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^2,x],x,1/x] /;
        FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[2*n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!((Atom::num(2) * &n_).expand(), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a1__ + &b1__ / sub_atom.pow(&n_)).pow(&p_)
                * (&a2__ + &b2__ / sub_atom.pow(&n_)).pow(&p_)
                / sub_atom.pow(2);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(
                &primitive,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 784,
        source: "Int[(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[2*n]},
          k \\[Star] Subst[Int[x^(k-1)*(a1+b1*x^(k*n))^p*(a2+b2*x^(k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && FractionQ[2*n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && fractionq!((Atom::num(2) * &n_).expand())
        },
        rhs: {
            let denominator = rubi_denominator(&(Atom::num(2) * &n_)).rubi_rhs();
            let k = Atom::num(denominator);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_exponent = &k * &n_;
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a1__ + &b1__ * sub_atom.pow(&transformed_exponent)).pow(&p_)
                * (&a2__ + &b2__ * sub_atom.pow(transformed_exponent)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                x_.pow(Atom::num(1) / &k),
            );

            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, b2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 785,
        source: "Int[(a1_.+b1_.*x_^n_)^p_*(a2_.+b2_.*x_^n_)^p_,x_Symbol] :=
          (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p] \\[Star] Int[(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,n,p},x] && EqQ[a2*b1+a1*b2,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [a1__, b1__, a2__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_part = rubi_frac_part(&p_);
            let first_binomial = &a1__ + &b1__ * x_.pow(&n_);
            let second_binomial = &a2__ + &b2__ * x_.pow(&n_);
            let combined_binomial = &a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&combined_binomial.pow(&p_), x_);
            let multiplier = first_binomial.pow(&frac_part) * second_binomial.pow(&frac_part)
                / combined_binomial.pow(frac_part);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 786,
        source: "Int[(a_+b_.*(c_.*x_^q_.)^n_)^p_,x_Symbol] :=
          x/(c*x^q)^(1/q) \\[Star] Subst[Int[(a+b*x^(n*q))^p,x],x,(c*x^q)^(1/q)] /;
        FreeQ[{a,b,c,n,p,q},x] && IntegerQ[n*q] && NeQ[x,(c*x^q)^(1/q)]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, q_, x_],
        optional: [b__, c__, q_],
        when: {
            let replacement = (&c__ * x_.pow(&q_)).pow(Atom::num(1) / &q_);
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && integerq!(&n_ * &q_)
                && rubi_branch_sensitive_ne_q(x_, &replacement)
        },
        rhs: {
            let scaled_monomial = &c__ * x_.pow(&q_);
            let replacement = scaled_monomial.pow(Atom::num(1) / &q_);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_ * &q_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, &replacement);

            rubi_star(x_ / replacement, substituted)
        },
    ));
}

fn push_rules_rule_787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 787,
        source: "Int[(a_+b_.*(c_.*x_^q_.)^n_)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          Subst[Int[(a+b*c^n*x^(n*q))^p,x],x^(1/k),(c*x^q)^(1/k)/(c^(1/k)*(x^(1/k))^(q-1))]] /;
        FreeQ[{a,b,c,p,q},x] && FractionQ[n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, q_, x_],
        optional: [b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, p_, q_], x_)
                && fractionq!(n_)
        },
        rhs: {
            let denominator = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(denominator);
            let transformed_integrand =
                (&a__ + &b__ * c__.pow(&n_) * x_.pow(&n_ * &q_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, x_);
            let x_root = x_.pow(Atom::num(1) / &k);
            let replacement = (&c__ * x_.pow(&q_)).pow(Atom::num(1) / &k)
                / (c__.pow(Atom::num(1) / &k) * x_root.pow(&q_ - Atom::num(1)));
            let target_exponent = Atom::num(1) / &k;

            rubi_subst_power_target(
                &primitive,
                x_,
                &Atom::num(1),
                &target_exponent,
                &replacement,
            )
        },
    ));
}

fn push_rules_rule_788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 788,
        source: "Int[(a_+b_.*(c_.*x_^q_.)^n_)^p_,x_Symbol] :=
          Subst[Int[(a+b*c^n*x^(n*q))^p,x],x^(n*q),(c*x^q)^n/c^n] /;
        FreeQ[{a,b,c,n,p,q},x] && Not[RationalQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, q_, x_],
        optional: [b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && !rationalq!(n_)
        },
        rhs: {
            let target_exponent = &n_ * &q_;
            let transformed_integrand =
                (&a__ + &b__ * c__.pow(&n_) * x_.pow(&target_exponent)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, x_);
            let replacement = (&c__ * x_.pow(&q_)).pow(&n_) / c__.pow(&n_);

            rubi_subst_power_target(
                &primitive,
                x_,
                &Atom::num(1),
                &target_exponent,
                &replacement,
            )
        },
    ));
}

fn push_rules_rule_789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 789,
        source: "Int[(a_+b_.*(d_.*x_^q_.)^n_)^p_,x_Symbol] :=
          -Subst[Int[(a+b*(d*x^(-q))^n)^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,d,n,p},x] && ILtQ[q,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, d__, n_, p_, q_, x_],
        optional: [b__, d__, q_],
        when: {
            freeq!([a__, b__, d__, n_, p_], x_)
                && iltq!(q_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * (&d__ / sub_atom.pow(&q_)).pow(&n_)).pow(&p_)
                    / sub_atom.pow(2);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(
                &primitive,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 790,
        source: "Int[(a_+b_.*(d_.*x_^q_.)^n_)^p_,x_Symbol] :=
          With[{s=Denominator[q]},
          s \\[Star] Subst[Int[x^(s-1)*(a+b*(d*x^(q*s))^n)^p,x],x,x^(1/s)]] /;
        FreeQ[{a,b,d,n,p},x] && FractionQ[q]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, d__, n_, p_, q_, x_],
        optional: [b__, d__, q_],
        when: {
            freeq!([a__, b__, d__, n_, p_], x_)
                && fractionq!(q_)
        },
        rhs: {
            let denominator = rubi_denominator(&q_).rubi_rhs();
            let s = Atom::num(denominator);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_q = &s * &q_;
            let transformed_integrand = sub_atom.pow(&s - Atom::num(1))
                * (&a__ + &b__ * (&d__ * sub_atom.pow(transformed_q)).pow(&n_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                x_.pow(Atom::num(1) / &s),
            );

            rubi_star(s, substituted)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a1__ + b1__ * x_.pow(n_)).pow(p_) * (a2__ + b2__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(q_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * (d__ * x_.pow(q_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((1, 4))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((3, 4))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((5, 4))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(3)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(n_))
}
