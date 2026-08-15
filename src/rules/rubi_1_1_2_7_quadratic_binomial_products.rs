use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_451(rules);
    push_rules_rule_452(rules);
    push_rules_rule_453(rules);
    push_rules_rule_454(rules);
    push_rules_rule_455(rules);
    push_rules_rule_456(rules);
    push_rules_rule_457(rules);
    push_rules_rule_458(rules);
    push_rules_rule_459(rules);
    push_rules_rule_460(rules);
    push_rules_rule_461(rules);
    push_rules_rule_462(rules);
    push_rules_rule_463(rules);
    push_rules_rule_464(rules);
    push_rules_rule_465(rules);
    push_rules_rule_466(rules);
    push_rules_rule_467(rules);
    push_rules_rule_468(rules);
    push_rules_rule_469(rules);
    push_rules_rule_470(rules);
    push_rules_rule_471(rules);
    push_rules_rule_472(rules);
    push_rules_rule_473(rules);
    push_rules_rule_474(rules);
    push_rules_rule_475(rules);
    push_rules_rule_476(rules);
    push_rules_rule_477(rules);
    push_rules_rule_478(rules);
    push_rules_rule_479(rules);
    push_rules_rule_480(rules);
    push_rules_rule_481(rules);
    push_rules_rule_482(rules);
    push_rules_rule_483(rules);
    push_rules_rule_484(rules);
    push_rules_rule_485(rules);
    push_rules_rule_486(rules);
    push_rules_rule_487(rules);
    push_rules_rule_488(rules);
    push_rules_rule_489(rules);
    push_rules_rule_490(rules);
    push_rules_rule_491(rules);
    push_rules_rule_492(rules);
    push_rules_rule_493(rules);
    push_rules_rule_494(rules);
    push_rules_rule_495(rules);
    push_rules_rule_496(rules);
    push_rules_rule_497(rules);
    push_rules_rule_498(rules);
    push_rules_rule_499(rules);
    push_rules_rule_500(rules);
    push_rules_rule_501(rules);
    push_rules_rule_502(rules);
    push_rules_rule_503(rules);
    push_rules_rule_504(rules);
    push_rules_rule_505(rules);
    push_rules_rule_506(rules);
    push_rules_rule_507(rules);
    push_rules_rule_508(rules);
    push_rules_rule_509(rules);
    push_rules_rule_510(rules);
    push_rules_rule_511(rules);
    push_rules_rule_512(rules);
    push_rules_rule_513(rules);
    push_rules_rule_514(rules);
    push_rules_rule_515(rules);
}

fn push_rules_rule_451(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 451,
        source: "Int[(c_+d_.*x_)/(a_+b_.*x_^2),x_Symbol] :=
          c^2/a \\[Star] Int[1/(c-d*x),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (&c__ - &d__ * x_)),
                x_,
            );
            rubi_star(c__.pow(2) / &a__, primitive)
        },
    ));
}

fn push_rules_rule_452(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 452,
        source: "Int[(c_+d_.*x_)/(a_+b_.*x_^2),x_Symbol] :=
          c \\[Star] Int[1/(a+b*x^2),x] + d \\[Star] Int[x/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c^2+a*d^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / &denominator), x_);
            let second = rubi_rhs_int(&(x_ / denominator), x_);
            rubi_star(c__, first) + rubi_star(d__, second)
        },
    ));
}

fn push_rules_rule_453(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 453,
        source: "Int[(c_+d_.*x_)/(a_+b_.*x_^2)^(3/2),x_Symbol] :=
          -(a*d-b*c*x)/(a*b*Sqrt[a+b*x^2]) /;
        FreeQ[{a,b,c,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ + d__ * x_) / (a__ + b__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            rubi_simp(&(-(&a__ * &d__ - &b__ * &c__ * x_)
                    / (&a__ * &b__ * (&a__ + &b__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_454(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 454,
        source: "Int[(c_+d_.*x_)*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a*d-b*c*x)/(2*a*b*(p+1))*(a+b*x^2)^(p+1) +
          c*(2*p+3)/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && ltq!(p_, -1)
                && neq!(p_, Atom::num(-3) / 2)
        },
        rhs: {
            let direct = (&a__ * &d__ - &b__ * &c__ * x_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let primitive = rubi_rhs_int(
                &(&a__ + &b__ * x_.pow(2)).pow(&p_ + 1),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(&c__ * (Atom::num(2) * &p_ + 3)
                            / (Atom::num(2) * &a__ * (&p_ + 1)), primitive)
        },
    ));
}

fn push_rules_rule_455(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 455,
        source: "Int[(c_+d_.*x_)*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          d*(a+b*x^2)^(p+1)/(2*b*(p+1)) + c \\[Star] Int[(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[LeQ[p,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && !leq!(p_, -1)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&d__ * quadratic.pow(&p_ + Atom::num(1))
                    / (Atom::num(2) * &b__ * (&p_ + Atom::num(1)))),
                x_,
            );
            let recursive = rubi_rhs_int(&quadratic.pow(&p_), x_);
            rubi_simp(&(direct), x_) + rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_456(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 456,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(c+d*x)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0] && Not[IntegerQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(p_) || gtq!(a__, 0) && gtq!(c__, 0) && !integerq!(n_))
        },
        rhs: {
            rubi_rhs_int(
                &((&c__ + &d__ * x_).pow(&n_ + &p_)
                    * (&a__ / &c__ + &b__ * x_ / &d__).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_457(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 457,
        source: "Int[(c_+d_.*x_)^2*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)*(a+b*x^2)^(p+1)/(b*(p+1)) - d^2*(p+2)/(b*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c^2+a*d^2,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(2) * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &d__ * &linear * quadratic.pow(&p_ + 1)
                / (&b__ * (&p_ + 1));
            let primitive = rubi_rhs_int(&quadratic.pow(&p_ + 1), x_);
            rubi_simp(&(direct), x_)
                    - rubi_star(d__.pow(2) * (&p_ + 2) / (&b__ * (&p_ + 1)), primitive)
        },
    ));
}

fn push_rules_rule_458(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 458,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(p+1)) /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+p,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + &p_, 0)
        },
        rhs: {
            rubi_simp(&(&d__
                    * (&c__ + &d__ * x_).pow(&n_ - 1)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / (&b__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_459(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 459,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(n+2*p+1)) +
          2*c*Simplify[n+p]/(n+2*p+1) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[Simplify[n+p],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(rubi_simplify(&(&n_ + &p_)), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let balance = &n_ + Atom::num(2) * &p_ + 1;
            let simplified = rubi_simplify(&(&n_ + &p_));
            let direct = &d__
                * linear.pow(&n_ - 1)
                * quadratic.pow(&p_ + 1)
                / (&b__ * &balance);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(2) * &c__ * simplified / balance, primitive)
        },
    ));
}

fn push_rules_rule_460(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 460,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -d*(c+d*x)^n*(a+b*x^2)^(p+1)/(b*c*n) /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && EqQ[n+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && eqq!(&n_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            rubi_simp(&(-&d__
                    * (&c__ + &d__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / (&b__ * &c__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_461(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 461,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -d*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*b*c*(n+p+1)) +
          Simplify[n+2*p+2]/(2*c*(n+p+1)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[Simplify[n+2*p+2],0] && (LtQ[n,-1] || GtQ[n+p,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            let simplified = rubi_simplify(&(&n_ + Atom::num(2) * &p_ + 2));
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(simplified, 0)
                && (ltq!(n_, -1) || gtq!(&n_ + &p_, 0))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &c__ * (&n_ + &p_ + 1);
            let simplified = rubi_simplify(&(&n_ + Atom::num(2) * &p_ + 2));
            let direct = -&d__ * linear.pow(&n_) * quadratic.pow(&p_ + 1)
                / (&b__ * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(simplified / denominator, primitive)
        },
    ));
}

fn push_rules_rule_462(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 462,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2)^(3/2),x_Symbol] :=
          -2^(n-1)*d*c^(n-2)*(c+d*x)/(b*Sqrt[a+b*x^2]) +
          d^2/b \\[Star] Int[1/Sqrt[a+b*x^2]*ExpandToSum[(2^(n-1)*c^(n-1)-(c+d*x)^(n-1))/(c-d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IGtQ[n,2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && igtq!(n_, 2)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -Atom::num(2).pow(&n_ - 1)
                * &d__
                * c__.pow(&n_ - 2)
                * &linear
                / (&b__ * quadratic.sqrt());
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(&n_ - 1) * c__.pow(&n_ - 1)
                    - linear.pow(&n_ - 1))
                    / (&c__ - &d__ * x_)),
                x_,
            );
            let primitive = rubi_rhs_int(&(payload / quadratic.sqrt()), x_);
            rubi_simp(&(direct), x_) + rubi_star(d__.pow(2) / &b__, primitive)
        },
    ));
}

fn push_rules_rule_463(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 463,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(-c)^(-n-2)*d^(2*n+3)*Sqrt[a+b*x^2]/(2^(n+1)*b^(n+2)*(c+d*x)) -
          d^(2*n+2)/b^(n+1) \\[Star] Int[1/Sqrt[a+b*x^2]*ExpandToSum[(2^(-n-1)*(-c)^(-n-1)-(-c+d*x)^(-n-1))/(c+d*x),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && ILtQ[n,0] && EqQ[n+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && iltq!(n_, 0)
                && eqq!(&n_ + &p_, Atom::num(-3) / 2)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -(-&c__).pow(-&n_ - 2)
                * d__.pow(Atom::num(2) * &n_ + 3)
                * quadratic.sqrt()
                / (Atom::num(2).pow(&n_ + 1) * b__.pow(&n_ + 2) * &linear);
            let payload = rubi_expand_to_sum(
                &((Atom::num(2).pow(-&n_ - 1) * (-&c__).pow(-&n_ - 1)
                    - (-&c__ + &d__ * x_).pow(-&n_ - 1))
                    / &linear),
                x_,
            );
            let primitive = rubi_rhs_int(&(payload / quadratic.sqrt()), x_);
            rubi_simp(&(direct), x_)
                    - rubi_star(d__.pow(Atom::num(2) * &n_ + 2) / b__.pow(&n_ + 1), primitive)
        },
    ));
}

fn push_rules_rule_464(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 464,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[(a+b*x^2)^(n+p)/(a/c+b*x/d)^n,x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && IntegerQ[n] && RationalQ[p] && (LtQ[0,-n,p] || LtQ[p,-n,0]) && NeQ[n,2] && NeQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && integerq!(n_)
                && rationalq!(p_)
                && (ltq!(0, -&n_, p_) || ltq!(p_, -&n_, 0))
                && neq!(n_, 2)
                && neq!(n_, -1)
        },
        rhs: {
            rubi_rhs_int(
                &((&a__ + &b__ * x_.pow(2)).pow(&n_ + &p_)
                    / (&a__ / &c__ + &b__ * x_ / &d__).pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_465(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 465,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(a+b*x^2)^p/(d*(n+p+1)) -
          b*p/(d^2*(n+p+1)) \\[Star] Int[(c+d*x)^(n+2)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && GtQ[p,0] && (LtQ[n,-2] || EqQ[n+2*p+1,0]) && NeQ[n+p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(p_, 0)
                && (ltq!(n_, -2) || eqq!(&n_ + Atom::num(2) * &p_ + 1, 0))
                && neq!(&n_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let balance = &n_ + &p_ + 1;
            let direct = linear.pow(&n_ + 1) * quadratic.pow(&p_)
                / (&d__ * &balance);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 2) * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(&b__ * &p_ / (d__.pow(2) * balance), primitive)
        },
    ));
}

fn push_rules_rule_466(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 466,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(a+b*x^2)^p/(d*(n+2*p+1)) -
          2*b*c*p/(d^2*(n+2*p+1)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && GtQ[p,0] && (LeQ[-2,n,0] || EqQ[n+p+1,0]) && NeQ[n+2*p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(p_, 0)
                && (leq!(-2, n_, 0) || eqq!(&n_ + &p_ + 1, 0))
                && neq!(&n_ + Atom::num(2) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let balance = &n_ + Atom::num(2) * &p_ + 1;
            let direct = linear.pow(&n_ + 1) * quadratic.pow(&p_)
                / (&d__ * &balance);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2) * &b__ * &c__ * &p_ / (d__.pow(2) * balance), primitive)
        },
    ));
}

fn push_rules_rule_467(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 467,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -c*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*a*d*(p+1)) +
          c*(n+2*p+2)/(2*a*(p+1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && LtQ[p,-1] && LtQ[0,n,1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && ltq!(p_, -1)
                && ltq!(0, n_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * (&p_ + 1);
            let direct = -&c__ * linear.pow(&n_) * quadratic.pow(&p_ + 1)
                / (&d__ * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(&c__ * (&n_ + Atom::num(2) * &p_ + 2) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_468(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 468,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(p+1)) -
          d^2*(n+p)/(b*(p+1)) \\[Star] Int[(c+d*x)^(n-2)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0] && LtQ[p,-1] && GtQ[n,1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&p_ + 1);
            let direct = &d__ * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 2) * quadratic.pow(&p_ + 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(d__.pow(2) * (&n_ + &p_) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_469(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 469,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(n+2*p+1)) +
          2*c*(n+p)/(n+2*p+1) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c^2+a*d^2,0] && GtQ[n,0] && NeQ[n+2*p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && gtq!(n_, 0)
                && neq!(&n_ + Atom::num(2) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let balance = &n_ + Atom::num(2) * &p_ + 1;
            let direct = &d__ * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)
                / (&b__ * &balance);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(2) * &c__ * (&n_ + &p_) / balance, primitive)
        },
    ));
}

fn push_rules_rule_470(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 470,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -d*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*b*c*(n+p+1)) +
          (n+2*p+2)/(2*c*(n+p+1)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c^2+a*d^2,0] && LtQ[n,0] && NeQ[n+p+1,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && ltq!(n_, 0)
                && neq!(&n_ + &p_ + 1, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &c__ * (&n_ + &p_ + 1);
            let direct = -&d__ * linear.pow(&n_) * quadratic.pow(&p_ + 1)
                / (&b__ * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star((&n_ + Atom::num(2) * &p_ + 2) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_471(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 471,
        source: "Int[1/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          2*d \\[Star] Subst[Int[1/(2*b*c+d^2*x^2),x],x,Sqrt[a+b*x^2]/Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+a*d^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (Atom::num(2) * &b__ * &c__ + d__.pow(2) * sub_atom.pow(2))),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&a__ + &b__ * x_.pow(2)).sqrt()
                    / (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) * &d__, substituted)
        },
    ));
}

fn push_rules_rule_472(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 472,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^(p+1)*c^(n-1)*((c-d*x)/c)^(p+1)/(a/c+b*x/d)^(p+1) \\[Star] Int[(1+d*x/c)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[n] || GtQ[c,0]) && GtQ[a,0] &&
          Not[IntegerQ[n] && (IntegerQ[3*p] || IntegerQ[4*p])]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(n_) || gtq!(c__, 0))
                && gtq!(a__, 0)
                && !(integerq!(n_)
                    && (integerq!(Atom::num(3) * &p_)
                        || integerq!(Atom::num(4) * &p_)))
        },
        rhs: {
            let multiplier = a__.pow(&p_ + 1)
                * c__.pow(&n_ - 1)
                * ((&c__ - &d__ * x_) / &c__).pow(&p_ + 1)
                / (&a__ / &c__ + &b__ * x_ / &d__).pow(&p_ + 1);
            let primitive = rubi_rhs_int(
                &((Atom::num(1) + &d__ * x_ / &c__).pow(&n_ + &p_)
                    * (&a__ / &c__ + &b__ * x_ / &d__).pow(&p_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_473(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 473,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^(n-1)*(a+b*x^2)^(p+1)/((1+d*x/c)^(p+1)*(a/c+(b*x)/d)^(p+1)) \\[Star] Int[(1+d*x/c)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[n] || GtQ[c,0]) && Not[GtQ[a,0]] &&
          Not[IntegerQ[n] && (IntegerQ[3*p] || IntegerQ[4*p])]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(n_) || gtq!(c__, 0))
                && !gtq!(a__, 0)
                && !(integerq!(n_)
                    && (integerq!(Atom::num(3) * &p_)
                        || integerq!(Atom::num(4) * &p_)))
        },
        rhs: {
            let normalized_linear = Atom::num(1) + &d__ * x_ / &c__;
            let normalized_other_linear = &a__ / &c__ + &b__ * x_ / &d__;
            let multiplier = c__.pow(&n_ - 1)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                / (normalized_linear.pow(&p_ + 1)
                    * normalized_other_linear.pow(&p_ + 1));
            let primitive = rubi_rhs_int(
                &(normalized_linear.pow(&n_ + &p_) * normalized_other_linear.pow(&p_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_474(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 474,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n] \\[Star] Int[(1+d*x/c)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[b*c^2+a*d^2,0] && Not[IntegerQ[n] || GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && !(integerq!(n_) || gtq!(c__, 0))
        },
        rhs: {
            let normalized_linear = Atom::num(1) + &d__ * x_ / &c__;
            let frac_part = rubi_frac_part(&n_);
            let multiplier = c__.pow(rubi_int_part(&n_))
                * (&c__ + &d__ * x_).pow(&frac_part)
                / normalized_linear.pow(&frac_part);
            let primitive = rubi_rhs_int(
                &(normalized_linear.pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_475(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 475,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          d*n*c^(n-1)*(a+b*x^2)^(p+1)/(2*b*(p+1)) +
          Int[ExpandIntegrand[((c+d*x)^n-d*n*c^(n-1)*x)*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0] && IGtQ[n,0] && LeQ[n,p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(p_, 0)
                && igtq!(n_, 0)
                && leq!(n_, p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&d__ * &n_ * c__.pow(&n_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / (Atom::num(2) * &b__ * (&p_ + Atom::num(1)))),
                x_,
            );
            let remainder = (linear.pow(&n_)
                - &d__ * &n_ * c__.pow(&n_ - Atom::num(1)) * x_)
                * quadratic.pow(&p_);
            let expanded = rubi_expand_integrand(&remainder, x_);

            rubi_simp(&(direct), x_) + rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_476(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 476,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c+d*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (c__ + d__ * x_).pow(n_)
                * (a__ + b__ * x_.pow(2)).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_477(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 477,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^p \\[Star] Int[ExpandIntegrand[(c+d*x)^n*(1-Rt[-b/a,2]*x)^p*(1+Rt[-b/a,2]*x)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[n] && NiceSqrtQ[-b/a] && Not[FractionalPowerFactorQ[Rt[-b/a,2]]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(n_)
                && rubi_nice_sqrt_q(&(-&b__ / &a__))
                && !rubi_fractional_power_factor_q(&rubi_rt(&(-&b__ / &a__), 2))
        },
        rhs: {
            let root = rubi_rt(&(-&b__ / &a__), 2);
            let payload = (&c__ + &d__ * x_).pow(&n_)
                * (Atom::num(1) - &root * x_).pow(&p_)
                * (Atom::num(1) + root * x_).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(a__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_478(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 478,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(c+d*x)^n/(a+b*x^2),x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(n_, 1) },
        rhs: {
            let expanded = rubi_expand_integrand(
                &((&c__ + &d__ * x_).pow(&n_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_479(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 479,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)),x_Symbol] :=
          d*Log[RemoveContent[c+d*x,x]]/(b*c^2+a*d^2) +
          b/(b*c^2+a*d^2) \\[Star] Int[(c-d*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: 1 / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = &d__ * rubi_remove_content(&(&c__ + &d__ * x_), x_).log()
                / &denominator;
            let primitive = rubi_rhs_int(
                &((&c__ - &d__ * x_) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&b__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_480(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 480,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          d*(c+d*x)^(n+1)/((n+1)*(b*c^2+a*d^2)) +
          b/(b*c^2+a*d^2) \\[Star] Int[(c+d*x)^(n+1)*(c-d*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(n_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = &d__ * linear.pow(&n_ + 1)
                / ((&n_ + 1) * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * (&c__ - &d__ * x_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&b__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_481(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 481,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          d*(c+d*x)^(n-1)/(b*(n-1)) +
          1/b \\[Star] Int[(c+d*x)^(n-2)*Simp[b*c^2-a*d^2+2*b*c*d*x,x]/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d},x] && GtQ[n,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && gtq!(n_, 1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &d__ * linear.pow(&n_ - 1) / (&b__ * (&n_ - 1));
            let numerator = rubi_simp(
                &(&b__ * c__.pow(2) - &a__ * d__.pow(2)
                    + Atom::num(2) * &b__ * &c__ * &d__ * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 2) * numerator / quadratic),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &b__, primitive)
        },
    ));
}

fn push_rules_rule_482(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 482,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          d*(c+d*x)^(n+1)/((n+1)*(b*c^2+a*d^2)) +
          b/(b*c^2+a*d^2) \\[Star] Int[(c+d*x)^(n+1)*(c-d*x)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,n},x] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && ltq!(n_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = &d__ * linear.pow(&n_ + 1)
                / ((&n_ + 1) * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * (&c__ - &d__ * x_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&b__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_483(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 483,
        source: "Int[Sqrt[c_+d_.*x_]/(a_+b_.*x_^2),x_Symbol] :=
          2*d \\[Star] Subst[Int[x^2/(b*c^2+a*d^2-2*b*c*x^2+b*x^4),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (c__ + d__ * x_).sqrt() / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2)
                + &b__ * sub_atom.pow(4);
            let primitive = rubi_rhs_int(&(sub_atom.pow(2) / denominator), sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) * &d__, substituted)
        },
    ));
}

fn push_rules_rule_484(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 484,
        source: "Int[1/(Sqrt[c_+d_.*x_]*(a_+b_.*x_^2)),x_Symbol] :=
          2*d \\[Star] Subst[Int[1/(b*c^2+a*d^2-2*b*c*x^2+b*x^4),x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: 1 / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2)
                + &b__ * sub_atom.pow(4);
            let primitive = rubi_rhs_int(&(Atom::num(1) / denominator), sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) * &d__, substituted)
        },
    ));
}

fn push_rules_rule_485(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 485,
        source: "Int[(c_+d_.*x_)^n_/(a_+b_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(c+d*x)^n,1/(a+b*x^2),x],x] /;
        FreeQ[{a,b,c,d,n},x] && Not[IntegerQ[2*n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).pow(&n_),
                &(Atom::num(1) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_486(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 486,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(a*d-b*c*x)*(a+b*x^2)^p/((n+1)*(b*c^2+a*d^2)) -
          2*a*b*p/((n+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^(n+2)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n+2*p+2,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&n_ + Atom::num(2) * &p_ + 2, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = (&n_ + 1) * (&b__ * c__.pow(2) + &a__ * d__.pow(2));
            let direct = linear.pow(&n_ + 1)
                * (&a__ * &d__ - &b__ * &c__ * x_)
                * quadratic.pow(&p_)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 2) * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2) * &a__ * &b__ * &p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_487(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 487,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n-1)*(a*d-b*c*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          (2*p+3)*(b*c^2+a*d^2)/(2*a*b*(p+1)) \\[Star] Int[(c+d*x)^(n-2)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n+2*p+2,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&n_ + Atom::num(2) * &p_ + 2, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &b__ * (&p_ + 1);
            let direct = linear.pow(&n_ - 1)
                * (&a__ * &d__ - &b__ * &c__ * x_)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 2) * quadratic.pow(&p_ + 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star((&p_ * 2 + 3)
                            * (&b__ * c__.pow(2) + &a__ * d__.pow(2))
                            / denominator, primitive)
        },
    ));
}

fn push_rules_rule_488(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 488,
        source: "Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          -Subst[Int[1/(b*c^2+a*d^2-x^2),x],x,(a*d-b*c*x)/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: 1 / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&b__ * c__.pow(2) + &a__ * d__.pow(2) - sub_atom.pow(2))),
                sub,
            );
            -rubi_subst(
                &primitive,
                sub,
                (&a__ * &d__ - &b__ * &c__ * x_)
                    / (&a__ + &b__ * x_.pow(2)).sqrt(),
            )
        },
    ));
}

fn push_rules_rule_489(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 489,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[-a*b,2]},
          (q-b*x)*(c+d*x)^(n+1)*(a+b*x^2)^p/((n+1)*(b*c+d*q)*((b*c+d*q)*(q+b*x)/((b*c-d*q)*(-q+b*x)))^p)*
            Hypergeometric2F1[n+1,-p,n+2,2*b*q*(c+d*x)/((b*c-d*q)*(q-b*x))]] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&n_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &b__), 2);
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first_linear = &q - &b__ * x_;
            let second_linear = &q + &b__ * x_;
            let first_coefficient = &b__ * &c__ + &d__ * &q;
            let second_coefficient = &b__ * &c__ - &d__ * &q;
            let powered_ratio = (&first_coefficient * &second_linear
                / (&second_coefficient * (-&q + &b__ * x_)))
                .pow(&p_);
            let argument = Atom::num(2) * &b__ * &q * &linear
                / (&second_coefficient * &first_linear);
            rubi_simp(&(first_linear
                    * linear.pow(&n_ + 1)
                    * quadratic.pow(&p_)
                    / ((&n_ + 1) * first_coefficient * powered_ratio)
                    * rubi_hypergeometric2f1(&n_ + 1, -&p_, &n_ + 2, argument)), x_)
        },
    ));
}

fn push_rules_rule_490(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 490,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -x*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*a*(p+1)) -
          c*n/(2*a*(p+1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n+2*p+3,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&n_ + Atom::num(2) * &p_ + 3, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * (&p_ + 1);
            let direct = Atom::num(-1) * x_ * linear.pow(&n_) * quadratic.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(&c__ * &n_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_491(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 491,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/((n+1)*(b*c^2+a*d^2)) +
          b*c/(b*c^2+a*d^2) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n+2*p+3,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&n_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * c__.pow(2) + &a__ * d__.pow(2);
            let direct = &d__ * linear.pow(&n_ + 1) * quadratic.pow(&p_ + 1)
                / ((&n_ + 1) * &denominator);
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1) * quadratic.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&b__ * &c__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_492(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 492,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(a+b*x^2)^p/(d*(n+1)) -
          2*b*p/(d*(n+1)) \\[Star] Int[x*(c+d*x)^(n+1)*(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,n},x] && GtQ[p,0] && (IntegerQ[p] || LtQ[n,-1]) && NeQ[n,-1] && Not[ILtQ[n+2*p+1,0]] && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && gtq!(p_, 0)
                && (integerq!(p_) || ltq!(n_, -1))
                && neq!(n_, -1)
                && !iltq!(&n_ + Atom::num(2) * &p_ + 1, 0)
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &d__ * (&n_ + 1);
            let direct = linear.pow(&n_ + 1) * quadratic.pow(&p_)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(x_ * linear.pow(&n_ + 1) * quadratic.pow(&p_ - 1)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2) * &b__ * &p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_493(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 493,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (c+d*x)^(n+1)*(a+b*x^2)^p/(d*(n+2*p+1)) +
          2*p/(d*(n+2*p+1)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^(p-1)*(a*d-b*c*x),x] /;
        FreeQ[{a,b,c,d,n},x] && GtQ[p,0] && NeQ[n+2*p+1,0] && (Not[RationalQ[n]] || LtQ[n,1]) && Not[ILtQ[n+2*p,0]] && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && gtq!(p_, 0)
                && neq!(&n_ + Atom::num(2) * &p_ + 1, 0)
                && (!rationalq!(n_) || ltq!(n_, 1))
                && !iltq!(&n_ + Atom::num(2) * &p_, 0)
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &d__ * (&n_ + Atom::num(2) * &p_ + 1);
            let direct = linear.pow(&n_ + 1) * quadratic.pow(&p_)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_)
                    * quadratic.pow(&p_ - 1)
                    * (&a__ * &d__ - &b__ * &c__ * x_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(2) * &p_ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_494(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 494,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -x*(c+d*x)^n*(a+b*x^2)^(p+1)/(2*a*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(c+d*x)^(n-1)*(a+b*x^2)^(p+1)*(c*(2*p+3)+d*(n+2*p+3)*x),x] /;
        FreeQ[{a,b,c,d},x] && LtQ[p,-1] && GtQ[n,0] && (LtQ[n,1] || ILtQ[n+2*p+3,0] && NeQ[n,2]) && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
                && (ltq!(n_, 1)
                    || iltq!(&n_ + Atom::num(2) * &p_ + 3, 0) && neq!(n_, 2))
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * (&p_ + 1);
            let direct = Atom::num(-1) * x_ * linear.pow(&n_) * quadratic.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 1)
                    * quadratic.pow(&p_ + 1)
                    * (&c__ * (Atom::num(2) * &p_ + 3)
                        + &d__ * (&n_ + Atom::num(2) * &p_ + 3) * x_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_495(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 495,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a*d-b*c*x)*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) -
          1/(2*a*b*(p+1)) \\[Star] Int[(c+d*x)^(n-2)*(a+b*x^2)^(p+1)*Simp[a*d^2*(n-1)-b*c^2*(2*p+3)-b*c*d*(n+2*p+2)*x,x],x] /;
        FreeQ[{a,b,c,d},x] && LtQ[p,-1] && GtQ[n,1] && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && ltq!(p_, -1)
                && gtq!(n_, 1)
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &b__ * (&p_ + 1);
            let direct = (&a__ * &d__ - &b__ * &c__ * x_)
                * linear.pow(&n_ - 1)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let simplified = rubi_simp(
                &(&a__ * d__.pow(2) * (&n_ - 1)
                    - &b__ * c__.pow(2) * (Atom::num(2) * &p_ + 3)
                    - &b__
                        * &c__
                        * &d__
                        * (&n_ + Atom::num(2) * &p_ + 2)
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 2) * quadratic.pow(&p_ + 1) * simplified),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_496(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 496,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          -(a*d+b*c*x)*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/(2*a*(p+1)*(b*c^2+a*d^2)) +
          1/(2*a*(p+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^n*(a+b*x^2)^(p+1)*Simp[b*c^2*(2*p+3)+a*d^2*(n+2*p+3)+b*c*d*(n+2*p+4)*x,x],x] /;
        FreeQ[{a,b,c,d,n},x] && LtQ[p,-1] && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && ltq!(p_, -1)
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2)
                * &a__
                * (&p_ + 1)
                * (&b__ * c__.pow(2) + &a__ * d__.pow(2));
            let direct = -(&a__ * &d__ + &b__ * &c__ * x_)
                * linear.pow(&n_ + 1)
                * quadratic.pow(&p_ + 1)
                / &denominator;
            let simplified = rubi_simp(
                &(&b__ * c__.pow(2) * (Atom::num(2) * &p_ + 3)
                    + &a__ * d__.pow(2) * (&n_ + Atom::num(2) * &p_ + 3)
                    + &b__
                        * &c__
                        * &d__
                        * (&n_ + Atom::num(2) * &p_ + 4)
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_ + 1) * simplified),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_497(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 497,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n-1)*(a+b*x^2)^(p+1)/(b*(n+2*p+1)) +
          1/(b*(n+2*p+1)) \\[Star] Int[(c+d*x)^(n-2)*(a+b*x^2)^p*Simp[b*c^2*(n+2*p+1)-a*d^2*(n-1)+2*b*c*d*(n+p)*x,x],x] /;
        FreeQ[{a,b,c,d,n,p},x] && If[RationalQ[n], GtQ[n,1], SumSimplerQ[n,-2]] && NeQ[n+2*p+1,0] && IntQuadraticQ[a,0,b,c,d,n,p,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && if rationalq!(n_) {
                    gtq!(n_, 1)
                } else {
                    sum_simplerq!(n_, -2)
                }
                && neq!(&n_ + Atom::num(2) * &p_ + 1, 0)
                && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &b__ * (&n_ + Atom::num(2) * &p_ + 1);
            let direct = &d__ * linear.pow(&n_ - 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let simplified = rubi_simp(
                &(&b__ * c__.pow(2) * (&n_ + Atom::num(2) * &p_ + 1)
                    - &a__ * d__.pow(2) * (&n_ - 1)
                    + Atom::num(2)
                        * &b__
                        * &c__
                        * &d__
                        * (&n_ + &p_)
                        * x_),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ - 2) * quadratic.pow(&p_) * simplified),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_498(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 498,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          d*(c+d*x)^(n+1)*(a+b*x^2)^(p+1)/((n+1)*(b*c^2+a*d^2)) +
          b/((n+1)*(b*c^2+a*d^2)) \\[Star] Int[(c+d*x)^(n+1)*(a+b*x^2)^p*(c*(n+1)-d*(n+2*p+3)*x),x] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[n,-1] && (LtQ[n,-1] && IntQuadraticQ[a,0,b,c,d,n,p,x] || SumSimplerQ[n,1] && IntegerQ[p] || ILtQ[Simplify[n+2*p+3],0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(n_, -1)
                && (ltq!(n_, -1)
                    && int_quadratic_q(&a__, &Atom::num(0), &b__, &c__, &d__, &n_, &p_)
                    || sum_simplerq!(n_, 1) && integerq!(p_)
                    || iltq!(rubi_simplify(&(&n_ + Atom::num(2) * &p_ + 3)), 0))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = (&n_ + 1) * (&b__ * c__.pow(2) + &a__ * d__.pow(2));
            let direct = &d__ * linear.pow(&n_ + 1) * quadratic.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(linear.pow(&n_ + 1)
                    * quadratic.pow(&p_)
                    * (&c__ * (&n_ + 1)
                        - &d__ * (&n_ + Atom::num(2) * &p_ + 3) * x_)),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(&b__ / denominator, primitive)
        },
    ));
}

fn push_rules_rule_499(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 499,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
          With[{q=Rt[-a,4]},
          1/(2*d*q)*ArcTan[c*q*(a+b*x^2)^(1/4)/(q^2*(c+d*x)-c*Sqrt[a+b*x^2])] -
          1/(2*d*q)*ArcTanh[c*q*(a+b*x^2)^(1/4)/(q^2*(c+d*x)+c*Sqrt[a+b*x^2])]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+2*a*d^2,0] && NegQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(2) * &a__ * d__.pow(2), 0)
                && negq!(a__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__), 4);
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let quarter_power = quadratic.pow((1, 4));
            let square_root = quadratic.sqrt();
            let numerator = &c__ * &q * &quarter_power;
            let first = (&numerator
                / (q.pow(2) * &linear - &c__ * &square_root))
                .atan();
            let second = (numerator
                / (q.pow(2) * linear + &c__ * square_root))
                .atanh();
            rubi_simp(&(first / (Atom::num(2) * &d__ * &q)), x_) - rubi_simp(&(second / (2 * &d__ * q)), x_)
        },
    ));
}

fn push_rules_rule_500(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 500,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
          (-a-b*x^2)^(1/4)/(a+b*x^2)^(1/4) \\[Star] Int[1/((c+d*x)*(-a-b*x^2)^(1/4)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+2*a*d^2,0] && PosQ[a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(2) * &a__ * d__.pow(2), 0)
                && posq!(a__)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let negative_quadratic = -&a__ - &b__ * x_.pow(2);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&c__ + &d__ * x_) * negative_quadratic.pow((1, 4)))),
                x_,
            );
            rubi_star(negative_quadratic.pow((1, 4)) / quadratic.pow((1, 4)), primitive)
        },
    ));
}

fn push_rules_rule_501(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 501,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)^(1/3)),x_Symbol] :=
          With[{q=Rt[6*b^2*d^2/c^2,3]},
          -Sqrt[3]*b*d*ArcTan[1/Sqrt[3]+2*b*(c-d*x)/(Sqrt[3]*c*q*(a+b*x^2)^(1/3))]/(c^2*q^2) -
          3*b*d*Log[c+d*x]/(2*c^2*q^2) +
          3*b*d*Log[b*c-b*d*x-c*q*(a+b*x^2)^(1/3)]/(2*c^2*q^2)] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2-3*a*d^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) - Atom::num(3) * &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_rt(
                &(Atom::num(6) * b__.pow(2) * d__.pow(2) / c__.pow(2)),
                3,
            );
            let sqrt_three = Atom::num(3).sqrt();
            let denominator = c__.pow(2) * q.pow(2);
            let arc_argument = Atom::num(1) / &sqrt_three
                + Atom::num(2) * &b__ * (&c__ - &d__ * x_)
                    / (&sqrt_three * &c__ * &q * quadratic.pow((1, 3)));
            let first = -&sqrt_three * &b__ * &d__ * arc_argument.atan() / &denominator;
            let second = -Atom::num(3) * &b__ * &d__ * linear.log()
                / (Atom::num(2) * &denominator);
            let third = Atom::num(3)
                * &b__
                * &d__
                * (&b__ * &c__
                    - &b__ * &d__ * x_
                    - &c__ * &q * quadratic.pow((1, 3)))
                    .log()
                / (Atom::num(2) * denominator);
            rubi_simp(&(first), x_) + rubi_simp(&(second), x_) + rubi_simp(&(third), x_)
        },
    ));
}

fn push_rules_rule_502(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 502,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)^(1/3)),x_Symbol] :=
          a^(1/3) \\[Star] Int[1/((c+d*x)*(1-3*d*x/c)^(1/3)*(1+3*d*x/c)^(1/3)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+9*a*d^2,0] && GtQ[a,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(9) * &a__ * d__.pow(2), 0)
                && gtq!(a__, 0)
        },
        rhs: {
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&c__ + &d__ * x_)
                        * (Atom::num(1) - Atom::num(3) * &d__ * x_ / &c__)
                            .pow((1, 3))
                        * (Atom::num(1) + Atom::num(3) * &d__ * x_ / &c__)
                            .pow((1, 3)))),
                x_,
            );
            rubi_star(a__.pow((1, 3)), primitive)
        },
    ));
}

fn push_rules_rule_503(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 503,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^2)^(1/3)),x_Symbol] :=
          (1+b*x^2/a)^(1/3)/(a+b*x^2)^(1/3) \\[Star] Int[1/((c+d*x)*(1+b*x^2/a)^(1/3)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^2+9*a*d^2,0] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(2) + Atom::num(9) * &a__ * d__.pow(2), 0)
                && !gtq!(a__, 0)
        },
        rhs: {
            let normalized_quadratic = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&c__ + &d__ * x_) * normalized_quadratic.pow((1, 3)))),
                x_,
            );
            rubi_star(normalized_quadratic.pow((1, 3))
                    / (&a__ + &b__ * x_.pow(2)).pow((1, 3)), primitive)
        },
    ));
}

fn push_rules_rule_504(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 504,
        source: "Int[(a_+b_.*x_^2)^p_/(c_+d_.*x_),x_Symbol] :=
          c \\[Star] Int[(a+b*x^2)^p/(c^2-d^2*x^2),x] - d \\[Star] Int[x*(a+b*x^2)^p/(c^2-d^2*x^2),x] /;
        FreeQ[{a,b,c,d,p},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, p_], x_) },
        rhs: {
            let quadratic_power = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let denominator = c__.pow(2) - d__.pow(2) * x_.pow(2);
            let first = rubi_rhs_int(&(&quadratic_power / &denominator), x_);
            let second = rubi_rhs_int(&(x_ * quadratic_power / denominator), x_);
            rubi_star(c__, first) - rubi_star(d__, second)
        },
    ));
}

fn push_rules_rule_505(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 505,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p,(c/(c^2-d^2*x^2)-d*x/(c^2-d^2*x^2))^(-n),x],x] /;
        FreeQ[{a,b,c,d,p},x] && ILtQ[n,-1] && PosQ[a/b]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && iltq!(n_, -1)
                && posq!(&a__ / &b__)
        },
        rhs: {
            let denominator = c__.pow(2) - d__.pow(2) * x_.pow(2);
            let transformed_linear = &c__ / &denominator - &d__ * x_ / denominator;
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * x_.pow(2)).pow(&p_),
                &transformed_linear.pow(-&n_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_506(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 506,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[-a/b,2]},
          -(a+b*x^2)^p*(1/(c+d*x))^(2*p)/(d*(1-(c-d*q)/(c+d*x))^p*(1-(c+d*q)/(c+d*x))^p) \\[Star]
            Subst[Int[(1-(c-d*q)*x)^p*(1-(c+d*q)*x)^p/x^(n+2*p+2),x],x,1/(c+d*x)]] /;
        FreeQ[{a,b,c,d,p},x] && ILtQ[n,-1] && NegQ[a/b]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && iltq!(n_, -1)
                && negq!(&a__ / &b__)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_rt(&(-&a__ / &b__), 2);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((Atom::num(1) - (&c__ - &d__ * &q) * &sub_atom).pow(&p_)
                    * (Atom::num(1) - (&c__ + &d__ * &q) * &sub_atom).pow(&p_)
                    / sub_atom.pow(&n_ + Atom::num(2) * &p_ + 2)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, Atom::num(1) / &linear);
            let multiplier = -quadratic.pow(&p_)
                * (Atom::num(1) / &linear).pow(Atom::num(2) * &p_)
                / (&d__
                    * (Atom::num(1) - (&c__ - &d__ * &q) / &linear).pow(&p_)
                    * (Atom::num(1) - (&c__ + &d__ * &q) / linear).pow(&p_));
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_507(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 507,
        source: "Int[Sqrt[c_+d_.*x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          2/d \\[Star] Subst[Int[x^2/Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2],x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let denominator = ((&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2))
                .sqrt();
            let primitive = rubi_rhs_int(&(sub_atom.pow(2) / denominator), sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_508(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 508,
        source: "Int[Sqrt[c_+d_.*x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          -2*Sqrt[c+d*x]/(Sqrt[a]*q*Sqrt[q*(c+d*x)/(d+c*q)]) \\[Star]
            Subst[Int[Sqrt[1-2*d*x^2/(d+c*q)]/Sqrt[1-x^2],x],x,Sqrt[(1-q*x)/2]]] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && GtQ[a,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&b__ / &a__)
                && gtq!(a__, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((Atom::num(1)
                    - Atom::num(2) * &d__ * sub_atom.pow(2) / (&d__ + &c__ * &q))
                    .sqrt()
                    / (Atom::num(1) - sub_atom.pow(2)).sqrt()),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                ((Atom::num(1) - &q * x_) / 2).sqrt(),
            );
            let multiplier = -Atom::num(2) * linear.sqrt()
                / (a__.sqrt()
                    * &q
                    * (&q * linear / (&d__ + &c__ * &q)).sqrt());
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_509(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 509,
        source: "Int[Sqrt[c_+d_.*x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[Sqrt[c+d*x]/Sqrt[1+b*x^2/a],x] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&b__ / &a__)
                && !gtq!(a__, 0)
        },
        rhs: {
            let normalized_quadratic = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(
                &((&c__ + &d__ * x_).sqrt() / &normalized_quadratic.sqrt()),
                x_,
            );
            rubi_star(normalized_quadratic.sqrt()
                    / (&a__ + &b__ * x_.pow(2)).sqrt(), primitive)
        },
    ));
}

fn push_rules_rule_510(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 510,
        source: "Int[1/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          2/d \\[Star] Subst[Int[1/Sqrt[(b*c^2+a*d^2)/d^2-2*b*c*x^2/d^2+b*x^4/d^2],x],x,Sqrt[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && posq!(&b__ / &a__) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let denominator = ((&b__ * c__.pow(2) + &a__ * d__.pow(2)) / d__.pow(2)
                - Atom::num(2) * &b__ * &c__ * sub_atom.pow(2) / d__.pow(2)
                + &b__ * sub_atom.pow(4) / d__.pow(2))
                .sqrt();
            let primitive = rubi_rhs_int(&(Atom::num(1) / denominator), sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&c__ + &d__ * x_).sqrt(),
            );
            rubi_star(Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_511(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 511,
        source: "Int[1/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          -2*Sqrt[q*(c+d*x)/(d+c*q)]/(Sqrt[a]*q*Sqrt[c+d*x]) \\[Star]
            Subst[Int[1/(Sqrt[1-2*d*x^2/(d+c*q)]*Sqrt[1-x^2]),x],x,Sqrt[(1-q*x)/2]]] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && GtQ[a,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&b__ / &a__)
                && gtq!(a__, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((Atom::num(1)
                        - Atom::num(2) * &d__ * sub_atom.pow(2) / (&d__ + &c__ * &q))
                        .sqrt()
                        * (Atom::num(1) - sub_atom.pow(2)).sqrt())),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                ((Atom::num(1) - &q * x_) / 2).sqrt(),
            );
            let multiplier = -Atom::num(2)
                * (&q * &linear / (&d__ + &c__ * &q)).sqrt()
                / (a__.sqrt() * &q * linear.sqrt());
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_512(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 512,
        source: "Int[1/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          Sqrt[1+b*x^2/a]/Sqrt[a+b*x^2] \\[Star] Int[1/(Sqrt[c+d*x]*Sqrt[1+b*x^2/a]),x] /;
        FreeQ[{a,b,c,d},x] && NegQ[b/a] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&b__ / &a__)
                && !gtq!(a__, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let normalized_quadratic = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (linear.sqrt() * &normalized_quadratic.sqrt())),
                x_,
            );
            rubi_star(normalized_quadratic.sqrt() / quadratic.sqrt(), primitive)
        },
    ));
}

fn push_rules_rule_513(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 513,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^p \\[Star] Int[(c+d*x)^n*(1+Rt[-b/a,2]*x)^p*(1-Rt[-b/a,2]*x)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && GtQ[a,0] && NegQ[b/a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && gtq!(a__, 0)
                && negq!(&b__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let primitive = rubi_rhs_int(
                &((&c__ + &d__ * x_).pow(&n_)
                    * (Atom::num(1) + &q * x_).pow(&p_)
                    * (Atom::num(1) - &q * x_).pow(&p_)),
                x_,
            );
            rubi_star(a__.pow(&p_), primitive)
        },
    ));
}

fn push_rules_rule_514(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 514,
        source: "Int[(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[-a/b,2]},
          (a+b*x^2)^p/(d*(1-(c+d*x)/(c-d*q))^p*(1-(c+d*x)/(c+d*q))^p) \\[Star]
            Subst[Int[x^n*Simp[1-x/(c+d*q),x]^p*Simp[1-x/(c-d*q),x]^p,x],x,c+d*x]] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c^2+a*d^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_rt(&(-&a__ / &b__), 2);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&n_)
                    * rubi_simp(
                        &(Atom::num(1) - &sub_atom / (&c__ + &d__ * &q)),
                        sub,
                    )
                    .pow(&p_)
                    * rubi_simp(
                        &(Atom::num(1) - &sub_atom / (&c__ - &d__ * &q)),
                        sub,
                    )
                    .pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, &linear);
            let multiplier = quadratic.pow(&p_)
                / (&d__
                    * (Atom::num(1) - &linear / (&c__ - &d__ * &q)).pow(&p_)
                    * (Atom::num(1) - linear / (&c__ + &d__ * &q)).pow(&p_));
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_515(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__);
    let rule = rubi_rule!(
        order: 515,
        source: "Int[(c_+d_.*u_)^n_.*(a_+b_.*u_^2)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(c+d*x)^n*(a+b*x^2)^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (c__ + d__ * u__).pow(n_) * (a__ + b__ * u__.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, u__, n_, p_, x_],
        optional: [b__, d__, n_, p_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, n_, p_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let primitive = rubi_rhs_int(
                &((&c__ + &d__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_)),
                x_,
            );
            let substituted = rubi_subst(&primitive, x_, u__);
            rubi_star(Atom::num(1) / coefficient, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn section_contains_every_downvalue_order_once() {
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

        assert_eq!(orders, (451..=515).collect::<Vec<_>>());
    }

    #[test]
    fn downvalue_477_expand_integrand_payload_has_only_linear_poles() {
        let t = symbol!("t");
        let payload = parse!("(a+t)^8*(1-t/b)^-1*(1+t/b)^-1");
        let expanded = rubi_expand_integrand(&payload, t);

        assert!(
            rubi_sum_q(&expanded),
            "expected a partial-fraction sum: {expanded}"
        );
        for term in rubi_add_terms(&expanded) {
            if let Some((_, denominator)) = rational_numerator_denominator(&term) {
                assert!(
                    polynomial_degree(&denominator, t).is_none_or(|degree| degree <= 1),
                    "DownValue 477 must produce polynomial terms or linear poles: {term}"
                );
            }
        }

        let residual = (expanded - payload).together();
        assert!(
            residual.is_zero(),
            "expanded payload is not equivalent: {residual}"
        );
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * x_).sqrt() / (a__ + b__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * x_) / (a__ + b__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    1 / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow((1, 3)))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    1 / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(2)).pow((1, 4)))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    1 / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2)).sqrt())
}
