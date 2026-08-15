use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5582(rules);
    push_rules_rule_5583(rules);
    push_rules_rule_5584(rules);
    push_rules_rule_5585(rules);
    push_rules_rule_5586(rules);
    push_rules_rule_5587(rules);
    push_rules_rule_5588(rules);
    push_rules_rule_5589(rules);
    push_rules_rule_5590(rules);
    push_rules_rule_5591(rules);
    push_rules_rule_5592(rules);
    push_rules_rule_5593(rules);
    push_rules_rule_5594(rules);
    push_rules_rule_5595(rules);
    push_rules_rule_5596(rules);
    push_rules_rule_5597(rules);
    push_rules_rule_5598(rules);
    push_rules_rule_5599(rules);
    push_rules_rule_5600(rules);
    push_rules_rule_5601(rules);
    push_rules_rule_5602(rules);
    push_rules_rule_5603(rules);
    push_rules_rule_5604(rules);
    push_rules_rule_5605(rules);
    push_rules_rule_5606(rules);
    push_rules_rule_5607(rules);
    push_rules_rule_5608(rules);
    push_rules_rule_5609(rules);
    push_rules_rule_5610(rules);
    push_rules_rule_5611(rules);
    push_rules_rule_5612(rules);
    push_rules_rule_5613(rules);
    push_rules_rule_5614(rules);
    push_rules_rule_5615(rules);
    push_rules_rule_5616(rules);
    push_rules_rule_5617(rules);
    push_rules_rule_5618(rules);
    push_rules_rule_5619(rules);
    push_rules_rule_5620(rules);
    push_rules_rule_5621(rules);
    push_rules_rule_5622(rules);
    push_rules_rule_5623(rules);
    push_rules_rule_5624(rules);
    push_rules_rule_5625(rules);
    push_rules_rule_5626(rules);
    push_rules_rule_5627(rules);
    push_rules_rule_5628(rules);
    push_rules_rule_5629(rules);
    push_rules_rule_5630(rules);
    push_rules_rule_5631(rules);
    push_rules_rule_5632(rules);
    push_rules_rule_5633(rules);
    push_rules_rule_5634(rules);
    push_rules_rule_5635(rules);
    push_rules_rule_5636(rules);
    push_rules_rule_5637(rules);
    push_rules_rule_5638(rules);
    push_rules_rule_5639(rules);
    push_rules_rule_5640(rules);
    push_rules_rule_5641(rules);
    push_rules_rule_5642(rules);
    push_rules_rule_5643(rules);
    push_rules_rule_5644(rules);
    push_rules_rule_5645(rules);
    push_rules_rule_5646(rules);
    push_rules_rule_5647(rules);
    push_rules_rule_5648(rules);
    push_rules_rule_5649(rules);
    push_rules_rule_5650(rules);
    push_rules_rule_5651(rules);
    push_rules_rule_5652(rules);
    push_rules_rule_5653(rules);
    push_rules_rule_5654(rules);
    push_rules_rule_5655(rules);
    push_rules_rule_5656(rules);
    push_rules_rule_5657(rules);
}

fn push_rules_rule_5582(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, n__, x_);
    rules.push(rubi_rule!(
        order: 5582,
        source: "Int[E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          Int[((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
        FreeQ[a,x] && IntegerQ[(I*n-1)/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [n__, a__, x_],
        optional: [a__],
        when: {
            freeq!(a__, x_)
                && integerq!((Atom::i() * &n__ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = (Atom::num(1) - &i * &a__ * x_)
                .pow((&i * &n__ + Atom::num(1)) / Atom::num(2))
                / ((Atom::num(1) + &i * &a__ * x_)
                    .pow((&i * &n__ - Atom::num(1)) / Atom::num(2))
                    * (Atom::num(1) + a__.pow(2) * x_.pow(2)).sqrt());
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5583(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n__, x_);
    rules.push(rubi_rule!(
        order: 5583,
        source: "Int[x_^m_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          Int[x^m*((1-I*a*x)^((I*n+1)/2)/((1+I*a*x)^((I*n-1)/2)*Sqrt[1+a^2*x^2])),x] /;
        FreeQ[{a,m},x] && IntegerQ[(I*n-1)/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, n__, a__, x_],
        optional: [m_, a__],
        when: {
            freeq!([a__, m_], x_)
                && integerq!((Atom::i() * &n__ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (Atom::num(1) - &i * &a__ * x_)
                    .pow((&i * &n__ + Atom::num(1)) / Atom::num(2))
                / ((Atom::num(1) + &i * &a__ * x_)
                    .pow((&i * &n__ - Atom::num(1)) / Atom::num(2))
                    * (Atom::num(1) + a__.pow(2) * x_.pow(2)).sqrt());
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5584(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, n__, x_);
    rules.push(rubi_rule!(
        order: 5584,
        source: "Int[E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          Int[(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
        FreeQ[{a,n},x] && Not[IntegerQ[(I*n-1)/2]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [n__, a__, x_],
        optional: [n__, a__],
        when: {
            freeq!([a__, n__], x_)
                && !integerq!((Atom::i() * &n__ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = (Atom::num(1) - &i * &a__ * x_).pow(&i * &n__ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n__ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5585(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n__, x_);
    rules.push(rubi_rule!(
        order: 5585,
        source: "Int[x_^m_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          Int[x^m*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
        FreeQ[{a,m,n},x] && Not[IntegerQ[(I*n-1)/2]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, n__, a__, x_],
        optional: [m_, n__, a__],
        when: {
            freeq!([a__, m_, n__], x_)
                && !integerq!((Atom::i() * &n__ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n__ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n__ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5586(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5586,
        source: "Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[u*(1+d*x/c)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && (IntegerQ[p] || GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(a__.pow(2) * c__.pow(2) + d__.pow(2), 0)
                && (integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (Atom::num(1) + &d__ * x_ / &c__).pow(&p_)
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_ / Atom::num(2));
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5587(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5587,
        source: "Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          Int[u*(c+d*x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(a__.pow(2) * c__.pow(2) + d__.pow(2), 0)
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (&c__ + &d__ * x_).pow(&p_)
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5588(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5588,
        source: "Int[u_.*(c_+d_./x_)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          d^p \\[Star] Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[c^2+a^2*d^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed = &u__
                * (Atom::num(1) + &c__ * x_ / &d__).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp()
                / x_.pow(&p_);
            rubi_star(d__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5589(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5589,
        source: "Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTanh[a_.*x_]),x_Symbol] :=
          (-1)^(n/2)*c^p \\[Star] Int[u*(1+d/(c*x))^p*(1-1/(I*a*x))^(I*n/2)/(1+1/(I*a*x))^(I*n/2),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && GtQ[c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ + d__ / x_).pow(p_) * (n_ * (a__ * x_).atanh()).exp(),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(p_)
                && integerq!(Atom::i() * &n_ / Atom::num(2))
                && gtq!(c__, 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (Atom::num(1) + &d__ / (&c__ * x_)).pow(&p_)
                * (Atom::num(1) - Atom::num(1) / (&i * &a__ * x_)).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + Atom::num(1) / (&i * &a__ * x_)).pow(&i * &n_ / Atom::num(2));
            rubi_star(Atom::num(-1).pow(&n_ / Atom::num(2)) * c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5590(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5590,
        source: "Int[u_.*(c_+d_./x_)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          Int[u*(c+d/x)^p*(1-I*a*x)^(I*n/2)/(1+I*a*x)^(I*n/2),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[GtQ[c,0]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(p_)
                && integerq!(Atom::i() * &n_ / Atom::num(2))
                && !gtq!(c__, 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (&c__ + &d__ / x_).pow(&p_)
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5591(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5591,
        source: "Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          x^p*(c+d/x)^p/(1+c*x/d)^p \\[Star] Int[u/x^p*(1+c*x/d)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(p_)
        },
        rhs: {
            let recursive = &u__
                * (Atom::num(1) + &c__ * x_ / &d__).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp()
                / x_.pow(&p_);
            rubi_star(x_.pow(&p_) * (&c__ + &d__ / x_).pow(&p_)
                    / (Atom::num(1) + &c__ * x_ / &d__).pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5592(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, capital_f_, d__, n_, x_);
    let exponential_pattern = capital_f_.pow(n_ * (a__ * x_).atan());
    rules.push(rubi_rule!(
        order: 5592,
        source: "Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
          (n+a*x)*E^(n*ArcTan[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: exponential_pattern / (c__ + d__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [capital_f_, n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            rubi_euler_symbol_q(&capital_f_)
                && freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!(Atom::i() * &n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&n_ * (&a__ * x_).atan());
            rubi_simp(&((&n_ + &a__ * x_) * exponential
                    / (&a__
                        * &c__
                        * (n_.pow(2) + 1)
                        * (&c__ + &d__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_5593(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5593,
        source: "Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          (n-2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*c*(n^2+4*(p+1)^2)) +
          2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2)) \\[Star] Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && ltq!(p_, -1)
                && !integerq!(Atom::i() * &n_)
                && neq!(n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2), 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2);
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).atan()).exp();
            let recursive = quadratic.pow(&p_ + 1) * &exponential;
            rubi_simp(&((&n_ - Atom::num(2) * &a__ * (&p_ + 1) * x_)
                    * quadratic.pow(&p_ + 1)
                    * exponential
                    / (&a__ * &c__ * &denominator)), x_)
                    + rubi_star(Atom::num(2) * (&p_ + 1) * (Atom::num(2) * &p_ + 3)
                            / (&c__ * denominator), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5594(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5594,
        source: "Int[E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
          E^(n*ArcTan[a*x])/(a*c*n) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (n_ * (a__ * x_).atan()).exp() / (c__ + d__ * x_.pow(2)),
        with: [n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
        },
        rhs: {
            rubi_simp(&((&n_ * (&a__ * x_).atan()).exp() / (&a__ * &c__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_5595(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5595,
        source: "Int[(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && IntegerQ[p] && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && integerq!(p_)
                && integerq!((Atom::i() * &n_ + Atom::num(1)) / Atom::num(2))
                && !integerq!(&p_ - Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = (Atom::num(1) + a__.pow(2) * x_.pow(2))
                    .pow(&p_ - &i * &n_ / Atom::num(2))
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_);
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5596(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n__, p_, x_);
    rules.push(rubi_rule!(
        order: 5596,
        source: "Int[(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, p_, n__, a__, x_],
        optional: [d__, p_, n__, a__],
        when: {
            freeq!([a__, c__, d__, n__, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && (integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = (Atom::num(1) - &i * &a__ * x_)
                    .pow(&p_ + &i * &n__ / Atom::num(2))
                * (Atom::num(1) + &i * &a__ * x_)
                    .pow(&p_ - &i * &n__ / Atom::num(2));
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5597(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5597,
        source: "Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^(I*n/2) \\[Star] Int[(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[I*n/2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
                && igtq!(Atom::i() * &n_ / Atom::num(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = (&c__ + &d__ * x_.pow(2))
                .pow(&p_ - &i * &n_ / Atom::num(2))
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_);
            rubi_star(c__.pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5598(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5598,
        source: "Int[(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          1/c^(I*n/2) \\[Star] Int[(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[I*n/2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
                && iltq!(Atom::i() * &n_ / Atom::num(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = (&c__ + &d__ * x_.pow(2))
                .pow(&p_ + &i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_);
            rubi_star(Atom::num(1) / c__.pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5599(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n__, p_, x_);
    rules.push(rubi_rule!(
        order: 5599,
        source: "Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p] \\[Star] Int[(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, p_, n__, a__, x_],
        optional: [d__, n__, a__],
        when: {
            freeq!([a__, c__, d__, n__, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive =
                (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_) * (&n__ * (&a__ * x_).atan()).exp();
            rubi_star(c__.pow(rubi_int_part(&p_)) * (&c__ + &d__ * x_.pow(2)).pow(&frac_p)
                    / (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(frac_p), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5600(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5600,
        source: "Int[x_*E^(n_.*ArcTan[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
          -(1-a*n*x)*E^(n*ArcTan[a*x])/(d*(n^2+1)*Sqrt[c+d*x^2]) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ * (n_ * (a__ * x_).atan()).exp()
            / (c__ + d__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!(Atom::i() * &n_)
        },
        rhs: {
            let exponential = (&n_ * (&a__ * x_).atan()).exp();
            rubi_simp(&(-(Atom::num(1) - &a__ * &n_ * x_)
                    * exponential
                    / (&d__ * (n_.pow(2) + 1) * (&c__ + &d__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_5601(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5601,
        source: "Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          (c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(2*d*(p+1)) - a*c*n/(2*d*(p+1)) \\[Star] Int[(c+d*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && IntegerQ[2*p]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp(),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && ltq!(p_, -1)
                && !integerq!(Atom::i() * &n_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).atan()).exp();
            let recursive = quadratic.pow(&p_) * &exponential;
            rubi_simp(&(quadratic.pow(&p_ + 1) * exponential / (Atom::num(2) * &d__ * (&p_ + 1))), x_)
                    + rubi_star(-(&a__ * &c__ * &n_) / (Atom::num(2) * &d__ * (&p_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5602(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n__, p_, x_);
    rules.push(rubi_rule!(
        order: 5602,
        source: "Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          -(1-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*n*(n^2+1)) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && EqQ[n^2-2*(p+1),0] && Not[IntegerQ[I*n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(2) * (c__ + d__ * x_.pow(2)).pow(p_) * (n__ * (a__ * x_).atan()).exp(),
        with: [c__, d__, p_, n__, a__, x_],
        optional: [d__, p_, n__, a__],
        when: {
            freeq!([a__, c__, d__, n__], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && eqq!(n__.pow(2) - Atom::num(2) * (&p_ + 1), 0)
                && !integerq!(Atom::i() * &n__)
        },
        rhs: {
            rubi_simp(&(-(Atom::num(1) - &a__ * &n__ * x_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&p_ + 1)
                    * (&n__ * (&a__ * x_).atan()).exp()
                    / (&a__ * &d__ * &n__ * (n__.pow(2) + 1))), x_)
        },
    ));
}

fn push_rules_rule_5603(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5603,
        source: "Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          -(n-2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x])/(a*d*(n^2+4*(p+1)^2)) +
          (n^2-2*(p+1))/(d*(n^2+4*(p+1)^2)) \\[Star] Int[(c+d*x^2)^(p+1)*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && Not[IntegerQ[I*n]] && NeQ[n^2+4*(p+1)^2,0] && IntegerQ[2*p]",
        desc: "Algebraic expansion and ???",
        refs: [],
        pattern: x_.pow(2) * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp(),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && ltq!(p_, -1)
                && !integerq!(Atom::i() * &n_)
                && neq!(n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2), 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2);
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).atan()).exp();
            let recursive = quadratic.pow(&p_ + 1) * &exponential;
            rubi_simp(&(-(&n_ - Atom::num(2) * (&p_ + 1) * &a__ * x_)
                    * quadratic.pow(&p_ + 1)
                    * exponential
                    / (&a__ * &d__ * &denominator)), x_)
                    + rubi_star((n_.pow(2) - Atom::num(2) * (&p_ + 1)) / (&d__ * denominator), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5604(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5604,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[x^m*(1+a^2*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[(I*n+1)/2] && Not[IntegerQ[p-I*n/2]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, p_, a__],
        when: {
            freeq!([a__, c__, d__, m_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && (integerq!(p_) || gtq!(c__, 0))
                && integerq!((Atom::i() * &n_ + Atom::num(1)) / Atom::num(2))
                && !integerq!(&p_ - Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (Atom::num(1) + a__.pow(2) * x_.pow(2))
                    .pow(&p_ - &i * &n_ / Atom::num(2))
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_);
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5605(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5605,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[x^m*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
        FreeQ[{a,c,d,m,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, m_, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && (integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (Atom::num(1) - &i * &a__ * x_)
                    .pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &a__ * x_)
                    .pow(&p_ - &i * &n_ / Atom::num(2));
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5606(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5606,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^(I*n/2) \\[Star] Int[x^m*(c+d*x^2)^(p-I*n/2)*(1-I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && IGtQ[I*n/2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, a__],
        when: {
            freeq!([a__, c__, d__, m_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
                && igtq!(Atom::i() * &n_ / Atom::num(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (&c__ + &d__ * x_.pow(2)).pow(&p_ - &i * &n_ / Atom::num(2))
                * (Atom::num(1) - &i * &a__ * x_).pow(&i * &n_);
            rubi_star(c__.pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5607(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5607,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          1/c^(I*n/2) \\[Star] Int[x^m*(c+d*x^2)^(p+I*n/2)/(1+I*a*x)^(I*n),x] /;
        FreeQ[{a,c,d,m,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && ILtQ[I*n/2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, a__],
        when: {
            freeq!([a__, c__, d__, m_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
                && iltq!(Atom::i() * &n_ / Atom::num(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = x_.pow(&m_)
                * (&c__ + &d__ * x_.pow(2)).pow(&p_ + &i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_);
            rubi_star(Atom::num(1) / c__.pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5608(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5608,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p] \\[Star] Int[x^m*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,m,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, m_, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive = x_.pow(&m_)
                * (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp();
            rubi_star(c__.pow(rubi_int_part(&p_)) * (&c__ + &d__ * x_.pow(2)).pow(&frac_p)
                    / (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(frac_p), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5609(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5609,
        source: "Int[u_*(c_+d_.*x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && (integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (Atom::num(1) - &i * &a__ * x_)
                    .pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &a__ * x_)
                    .pow(&p_ - &i * &n_ / Atom::num(2));
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5610(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5610,
        source: "Int[u_*(c_+d_.*x_^2)^p_.*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^IntPart[p]*(c+d*x^2)^FracPart[p]/((1-I*a*x)^FracPart[p]*(1+I*a*x)^FracPart[p]) \\[Star]
            Int[u*(1-I*a*x)^(p+I*n/2)*(1+I*a*x)^(p-I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[I*n/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && (integerq!(p_) || gtq!(c__, 0))
                && integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let frac_p = rubi_frac_part(&p_);
            let transformed = &u__
                * (Atom::num(1) - &i * &a__ * x_)
                    .pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &a__ * x_)
                    .pow(&p_ - &i * &n_ / Atom::num(2));
            rubi_star(c__.pow(rubi_int_part(&p_)) * (&c__ + &d__ * x_.pow(2)).pow(&frac_p)
                    / ((Atom::num(1) - &i * &a__ * x_).pow(&frac_p)
                        * (Atom::num(1) + &i * &a__ * x_).pow(frac_p)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5611(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5611,
        source: "Int[u_*(c_+d_.*x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          c^IntPart[p]*(c+d*x^2)^FracPart[p]/(1+a^2*x^2)^FracPart[p] \\[Star] Int[u*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[p] || GtQ[c,0]] && Not[IntegerQ[I*n/2]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !(integerq!(p_) || gtq!(c__, 0))
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive = &u__
                * (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp();
            rubi_star(c__.pow(rubi_int_part(&p_)) * (&c__ + &d__ * x_.pow(2)).pow(&frac_p)
                    / (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(frac_p), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5612(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5612,
        source: "Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          d^p \\[Star] Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[c-a^2*d,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(&c__ - a__.pow(2) * &d__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed = &u__ * (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp()
                / x_.pow(Atom::num(2) * &p_);
            rubi_star(d__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5613(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5613,
        source: "Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          c^p \\[Star] Int[u*(1-I/(a*x))^p*(1+I/(a*x))^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && GtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(&c__ - a__.pow(2) * &d__, 0)
                && !integerq!(p_)
                && integerq!(Atom::i() * &n_ / Atom::num(2))
                && gtq!(c__, 0)
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (Atom::num(1) - &i / (&a__ * x_)).pow(&p_)
                * (Atom::num(1) + &i / (&a__ * x_)).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp();
            rubi_star(c__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5614(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5614,
        source: "Int[u_.*(c_+d_./x_^2)^p_*E^(n_*ArcTan[a_.*x_]),x_Symbol] :=
          x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p \\[Star] Int[u*(1+a^2*x^2)^(I*n/2+p)/(x^(2*p)*(1+I*a*x)^(I*n)),x] /;
        FreeQ[{a,c,d,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && IntegerQ[I*n/2] && Not[GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, a__],
        when: {
            freeq!([a__, c__, d__, p_], x_)
                && eqq!(&c__ - a__.pow(2) * &d__, 0)
                && !integerq!(p_)
                && integerq!(Atom::i() * &n_ / Atom::num(2))
                && !gtq!(c__, 0)
        },
        rhs: {
            let i = Atom::i();
            let normalized = Atom::num(1) + a__.pow(2) * x_.pow(2);
            let recursive = &u__ * normalized.pow(&i * &n_ / Atom::num(2) + &p_)
                / (x_.pow(Atom::num(2) * &p_)
                    * (Atom::num(1) + &i * &a__ * x_).pow(&i * &n_));
            rubi_star(x_.pow(Atom::num(2) * &p_)
                    * (&c__ + &d__ / x_.pow(2)).pow(&p_)
                    / normalized.pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5615(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5615,
        source: "Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcTan[a_.*x_]),x_Symbol] :=
          x^(2*p)*(c+d/x^2)^p/(1+a^2*x^2)^p \\[Star] Int[u/x^(2*p)*(1+a^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c-a^2*d,0] && Not[IntegerQ[p]] && Not[IntegerQ[I*n/2]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(&c__ - a__.pow(2) * &d__, 0)
                && !integerq!(p_)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let recursive = &u__ * (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_)
                * (&n_ * (&a__ * x_).atan()).exp()
                / x_.pow(Atom::num(2) * &p_);
            rubi_star(x_.pow(Atom::num(2) * &p_)
                    * (&c__ + &d__ / x_.pow(2)).pow(&p_)
                    / (Atom::num(1) + a__.pow(2) * x_.pow(2)).pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5616(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5616,
        source: "Int[E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
          Int[(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (n_ * (c__ * (a_ + b__ * x_)).atan()).exp(),
        with: [n_, c__, a_, b__, x_],
        optional: [n_, c__, b__],
        when: { freeq!([a_, b__, c__, n_], x_) },
        rhs: {
            let i = Atom::i();
            let transformed = (Atom::num(1) - &i * &a_ * &c__ - &i * &b__ * &c__ * x_)
                .pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_)
                    .pow(&i * &n_ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5617(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5617,
        source: "Int[x_^m_*E^(n_*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
          4/(I^m*n*b^(m+1)*c^(m+1)) \\[Star]
            Subst[Int[x^(2/(I*n))*(1-I*a*c-(1+I*a*c)*x^(2/(I*n)))^m/(1+x^(2/(I*n)))^(m+2),x],x,
              (1-I*c*(a+b*x))^(I*n/2)/(1+I*c*(a+b*x))^(I*n/2)] /;
        FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,I*n,1]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (n_ * (c__ * (a_ + b__ * x_)).atan()).exp(),
        with: [m_, n_, c__, a_, b__, x_],
        optional: [c__, b__],
        when: { freeq!([a_, b__, c__], x_) && iltq!(m_, 0) && ltq!(-1, Atom::i() * &n_, 1) },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let sub_power = sub_atom.pow(Atom::num(2) / (&i * &n_));
            let payload = &sub_power
                * (Atom::num(1)
                    - &i * &a_ * &c__
                    - (Atom::num(1) + &i * &a_ * &c__) * &sub_power)
                .pow(&m_)
                / (Atom::num(1) + sub_power).pow(&m_ + 2);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let affine = &a_ + &b__ * x_;
            let substitution = (Atom::num(1) - &i * &c__ * &affine).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &c__ * affine).pow(&i * &n_ / Atom::num(2));
            rubi_star(Atom::num(4)
                    / (i.pow(&m_) * &n_ * b__.pow(&m_ + 1) * c__.pow(&m_ + 1)), rubi_subst(&primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_5618(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5618,
        source: "Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcTan[c_.*(a_+b_.*x_)]),x_Symbol] :=
          Int[(d+e*x)^m*(1-I*a*c-I*b*c*x)^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (n_ * (c__ * (a_ + b__ * x_)).atan()).exp(),
        with: [d__, e__, m_, n_, c__, a_, b__, x_],
        optional: [d__, e__, m_, n_, c__, b__],
        when: { freeq!([a_, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let i = Atom::i();
            let transformed = (&d__ + &e__ * x_).pow(&m_)
                * (Atom::num(1) - &i * &a_ * &c__ - &i * &b__ * &c__ * x_)
                    .pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_)
                    .pow(&i * &n_ / Atom::num(2));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5619(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c__, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5619,
        source: "Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
          (c/(1+a^2))^p \\[Star] Int[u*(1-I*a-I*b*x)^(p+I*n/2)*(1+I*a+I*b*x)^(p-I*n/2),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,2*a*e] && EqQ[b^2*c-e(1+a^2),0] && (IntegerQ[p] || GtQ[c/(1+a^2),0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, c__, d__, e__, p_, n_, a_, b__, x_],
        optional: [u__, d__, e__, p_, n_, b__],
        when: {
            freeq!([a_, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(&b__ * &d__, Atom::num(2) * &a_ * &e__)
                && eqq!(b__.pow(2) * &c__ - &e__ * (Atom::num(1) + a_.pow(2)), 0)
                && (integerq!(p_) || gtq!(&c__ / (Atom::num(1) + a_.pow(2)), 0))
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__
                * (Atom::num(1) - &i * &a_ - &i * &b__ * x_)
                    .pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &a_ + &i * &b__ * x_)
                    .pow(&p_ - &i * &n_ / Atom::num(2));
            rubi_star((&c__ / (Atom::num(1) + a_.pow(2))).pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5620(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c__, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5620,
        source: "Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcTan[a_+b_.*x_]),x_Symbol] :=
          (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p \\[Star] Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcTan[a*x]),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d,2*a*e] && EqQ[b^2*c-e(1+a^2),0] && Not[IntegerQ[p] || GtQ[c/(1+a^2),0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u__, c__, d__, e__, p_, n_, a_, b__, x_],
        optional: [u__, d__, e__, p_, n_, b__],
        when: {
            freeq!([a_, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(&b__ * &d__, Atom::num(2) * &a_ * &e__)
                && eqq!(b__.pow(2) * &c__ - &e__ * (Atom::num(1) + a_.pow(2)), 0)
                && !(integerq!(p_) || gtq!(&c__ / (Atom::num(1) + a_.pow(2)), 0))
        },
        rhs: {
            let quadratic = &c__ + &d__ * x_ + &e__ * x_.pow(2);
            let reduced_quadratic =
                Atom::num(1) + a_.pow(2) + Atom::num(2) * &a_ * &b__ * x_ + b__.pow(2) * x_.pow(2);
            let recursive =
                &u__ * reduced_quadratic.pow(&p_) * (&n_ * (&a_ * x_).atan()).exp();
            rubi_star(quadratic.pow(&p_) / reduced_quadratic.pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5621(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5621,
        source: "Int[u_.*E^(n_.*ArcTan[c_./(a_.+b_.*x_)]),x_Symbol] :=
          Int[u*E^(n*ArcCot[a/c+b*x/c]),x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (n_ * (c__ / (a__ + b__ * x_)).atan()).exp(),
        with: [u__, n_, c__, a__, b__, x_],
        optional: [u__, n_, c__, a__, b__],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let transformed = &u__ * (&n_ * (&a__ / &c__ + &b__ * x_ / &c__).acot()).exp();
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5622(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5622,
        source: "Int[u_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
          (-1)^(I*n/2) \\[Star] Int[u*E^(-n*ArcTan[a*x]),x] /;
        FreeQ[a,x] && IntegerQ[I*n/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (n_ * (a__ * x_).acot()).exp(),
        with: [u__, n_, a__, x_],
        optional: [u__, a__],
        when: { freeq!(a__, x_) && integerq!(Atom::i() * &n_ / Atom::num(2)) },
        rhs: {
            let i = Atom::i();
            let transformed = &u__ * (-&n_ * (&a__ * x_).atan()).exp();
            rubi_star((-Atom::num(1)).pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5623(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, n_, x_);
    rules.push(rubi_rule!(
        order: 5623,
        source: "Int[E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
          -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^2*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
        FreeQ[a,x] && IntegerQ[(I*n-1)/2]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [n_, a__, x_],
        optional: [a__],
        when: {
            freeq!(a__, x_)
                && integerq!((Atom::i() * &n_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__)
                .pow((&i * &n_ + Atom::num(1)) / Atom::num(2))
                / (sub_atom.pow(2)
                    * (Atom::num(1) + &i * &sub_atom / &a__)
                        .pow((&i * &n_ - Atom::num(1)) / Atom::num(2))
                    * (Atom::num(1) + sub_atom.pow(2) / a__.pow(2)).sqrt());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5624(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5624,
        source: "Int[x_^m_.*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
          -Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
        FreeQ[a,x] && IntegerQ[(I*n-1)/2] && IntegerQ[m]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, n_, a__, x_],
        optional: [m_, a__],
        when: {
            freeq!(a__, x_)
                && integerq!((Atom::i() * &n_ - Atom::num(1)) / Atom::num(2))
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__)
                .pow((&i * &n_ + Atom::num(1)) / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__)
                        .pow((&i * &n_ - Atom::num(1)) / Atom::num(2))
                    * (Atom::num(1) + sub_atom.pow(2) / a__.pow(2)).sqrt());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5625(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, n_, x_);
    rules.push(rubi_rule!(
        order: 5625,
        source: "Int[E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -Subst[Int[(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
        FreeQ[{a,n},x] && Not[IntegerQ[I*n]]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [n_, a__, x_],
        optional: [n_, a__],
        when: { freeq!([a__, n_], x_) && !integerq!(Atom::i() * &n_) },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2))
                / (sub_atom.pow(2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5626(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5626,
        source: "Int[x_^m_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
        FreeQ[{a,n},x] && Not[IntegerQ[I*n]] && IntegerQ[m]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, n_, a__, x_],
        optional: [m_, n_, a__],
        when: { freeq!([a__, n_], x_) && !integerq!(Atom::i() * &n_) && integerq!(m_) },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&n_ / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5627(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5627,
        source: "Int[x_^m_*E^(n_*ArcCot[a_.*x_]),x_Symbol] :=
          -x^m*(1/x)^m \\[Star] Subst[Int[(1-I*x/a)^((I*n+1)/2)/(x^(m+2)*(1+I*x/a)^((I*n-1)/2)*Sqrt[1+x^2/a^2]),x],x,1/x] /;
        FreeQ[{a,m},x] && IntegerQ[(I*n-1)/2] && Not[IntegerQ[m]]",
        desc: "Algebraic simplification, piecewise constant extraction and integration by substitution!",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, n_, a__, x_],
        optional: [a__],
        when: {
            freeq!([a__, m_], x_)
                && integerq!((Atom::i() * &n_ - Atom::num(1)) / Atom::num(2))
                && !integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__)
                .pow((&i * &n_ + Atom::num(1)) / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__)
                        .pow((&i * &n_ - Atom::num(1)) / Atom::num(2))
                    * (Atom::num(1) + sub_atom.pow(2) / a__.pow(2)).sqrt());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(-1) * x_.pow(&m_) * (Atom::num(1) / x_).pow(&m_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5628(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5628,
        source: "Int[x_^m_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -Subst[Int[(1-I*x/a)^(n/2)/(x^(m+2)*(1+I*x/a)^(n/2)),x],x,1/x] /;
        FreeQ[{a,m,n},x] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[m]]",
        desc: "Algebraic simplification, piecewise constant extraction and integration by substitution!",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, n_, a__, x_],
        optional: [n_, a__],
        when: {
            freeq!([a__, m_, n_], x_)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&n_ / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5629(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5629,
        source: "Int[u_.*(c_+d_.*x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          d^p \\[Star] Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[I*n/2]] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) * c__.pow(2) + d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && integerq!(p_)
        },
        rhs: {
            let transformed = &u__
                * x_.pow(&p_)
                * (Atom::num(1) + &c__ / (&d__ * x_)).pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star(d__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5630(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5630,
        source: "Int[u_.*(c_+d_.*x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (c+d*x)^p/(x^p*(1+c/(d*x))^p) \\[Star] Int[u*x^p*(1+c/(d*x))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[a^2*c^2+d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(a__.pow(2) * c__.pow(2) + d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !integerq!(p_)
        },
        rhs: {
            let recursive = &u__
                * x_.pow(&p_)
                * (Atom::num(1) + &c__ / (&d__ * x_)).pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star((&c__ + &d__ * x_).pow(&p_)
                    / (x_.pow(&p_) * (Atom::num(1) + &c__ / (&d__ * x_)).pow(&p_)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5631(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5631,
        source: "Int[(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p \\[Star] Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^2*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0])",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) + &d__ * &sub_atom / &c__).pow(&p_)
                * (Atom::num(1) - &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2))
                / (sub_atom.pow(2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5632(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5632,
        source: "Int[x_^m_.*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p \\[Star] Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
        FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegerQ[m]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, m_, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) + &d__ * &sub_atom / &c__).pow(&p_)
                * (Atom::num(1) - &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5633(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5633,
        source: "Int[(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (c+d/x)^p/(1+d/(c*x))^p \\[Star] Int[(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let recursive = (Atom::num(1) + &d__ / (&c__ * x_)).pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star((&c__ + &d__ / x_).pow(&p_)
                    / (Atom::num(1) + &d__ / (&c__ * x_)).pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5634(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5634,
        source: "Int[x_^m_*(c_+d_./x_)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p*x^m*(1/x)^m \\[Star] Subst[Int[(1+d*x/c)^p*(1-I*x/a)^(I*n/2)/(x^(m+2)*(1+I*x/a)^(I*n/2)),x],x,1/x] /;
        FreeQ[{a,c,d,m,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[m]]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, m_, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && !integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) + &d__ * &sub_atom / &c__).pow(&p_)
                * (Atom::num(1) - &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2))
                / (sub_atom.pow(&m_ + 2)
                    * (Atom::num(1) + &i * &sub_atom / &a__).pow(&i * &n_ / Atom::num(2)));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_) * x_.pow(&m_) * (Atom::num(1) / x_).pow(&m_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5635(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5635,
        source: "Int[u_.*(c_+d_./x_)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (c+d/x)^p/(1+d/(c*x))^p \\[Star] Int[u*(1+d/(c*x))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c^2+a^2*d^2,0] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ + d__ / x_).pow(p_) * (n_ * (a__ * x_).acot()).exp(),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__.pow(2) + a__.pow(2) * d__.pow(2), 0)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let recursive = &u__
                * (Atom::num(1) + &d__ / (&c__ * x_)).pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star((&c__ + &d__ / x_).pow(&p_)
                    / (Atom::num(1) + &d__ / (&c__ * x_)).pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5636(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5636,
        source: "Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2),x_Symbol] :=
          -E^(n*ArcCot[a*x])/(a*c*n) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (n_ * (a__ * x_).acot()).exp() / (c__ + d__ * x_.pow(2)),
        with: [n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
        },
        rhs: {
            rubi_simp(&(-(&n_ * (&a__ * x_).acot()).exp() / (&a__ * &c__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_5637(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5637,
        source: "Int[E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
          -(n-a*x)*E^(n*ArcCot[a*x])/(a*c*(n^2+1)*Sqrt[c+d*x^2]) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[(I*n-1)/2]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (n_ * (a__ * x_).acot()).exp() / (c__ + d__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!((Atom::i() * &n_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            rubi_simp(&(-(&n_ - &a__ * x_) * (&n_ * (&a__ * x_).acot()).exp()
                    / (&a__
                        * &c__
                        * (n_.pow(2) + 1)
                        * (&c__ + &d__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_5638(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5638,
        source: "Int[(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -(n+2*a*(p+1)*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a*c*(n^2+4*(p+1)^2)) +
          2*(p+1)*(2*p+3)/(c*(n^2+4*(p+1)^2)) \\[Star] Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LtQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2+4*(p+1)^2,0] &&
          Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp(),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && ltq!(p_, -1)
                && neq!(p_, -Atom::num(3) / Atom::num(2))
                && neq!(n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2), 0)
                && !(integerq!(p_) && integerq!(&i * &n_ / Atom::num(2)))
                && !(!integerq!(p_) && integerq!((&i * &n_ - Atom::num(1)) / Atom::num(2)))
        },
        rhs: {
            let denominator = n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2);
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).acot()).exp();
            let recursive = quadratic.pow(&p_ + 1) * &exponential;
            rubi_simp(&(-(&n_ + Atom::num(2) * &a__ * (&p_ + 1) * x_)
                    * quadratic.pow(&p_ + 1)
                    * exponential
                    / (&a__ * &c__ * &denominator)), x_)
                    + rubi_star(Atom::num(2) * (&p_ + 1) * (Atom::num(2) * &p_ + 3)
                            / (&c__ * denominator), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5639(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5639,
        source: "Int[x_*E^(n_.*ArcCot[a_.*x_])/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
          -(1+a*n*x)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+1)*Sqrt[c+d*x^2]) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[(I*n-1)/2]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ * (n_ * (a__ * x_).acot()).exp() / (c__ + d__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [n_, a__, c__, d__, x_],
        optional: [n_, a__, d__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!((Atom::i() * &n_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            rubi_simp(&(-(Atom::num(1) + &a__ * &n_ * x_)
                    * (&n_ * (&a__ * x_).acot()).exp()
                    / (a__.pow(2) * &c__ * (n_.pow(2) + 1) * (&c__ + &d__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_5640(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5640,
        source: "Int[x_*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (2*(p+1)-a*n*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^2*c*(n^2+4*(p+1)^2)) +
          n*(2*p+3)/(a*c*(n^2+4*(p+1)^2)) \\[Star] Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LeQ[p,-1] && NeQ[p,-3/2] && NeQ[n^2+4*(p+1)^2,0] &&
          Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_ * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp(),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && leq!(p_, -1)
                && neq!(p_, -Atom::num(3) / Atom::num(2))
                && neq!(n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2), 0)
                && !(integerq!(p_) && integerq!(&i * &n_ / Atom::num(2)))
                && !(!integerq!(p_) && integerq!((&i * &n_ - Atom::num(1)) / Atom::num(2)))
        },
        rhs: {
            let denominator = n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2);
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).acot()).exp();
            let recursive = quadratic.pow(&p_ + 1) * &exponential;
            rubi_simp(&((Atom::num(2) * (&p_ + 1) - &a__ * &n_ * x_)
                    * quadratic.pow(&p_ + 1)
                    * exponential
                    / (a__.pow(2) * &c__ * &denominator)), x_)
                    + rubi_star(&n_ * (Atom::num(2) * &p_ + 3) / (&a__ * &c__ * denominator), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5641(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5641,
        source: "Int[x_^2*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*n^2*(n^2+1)) /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && EqQ[n^2-2*(p+1),0] && NeQ[n^2+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && eqq!(n_.pow(2) - Atom::num(2) * (&p_ + 1), 0)
                && neq!(n_.pow(2) + 1, 0)
        },
        rhs: {
            rubi_simp(&((&n_ + Atom::num(2) * (&p_ + 1) * &a__ * x_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&p_ + 1)
                    * (&n_ * (&a__ * x_).acot()).exp()
                    / (a__.pow(3) * &c__ * n_.pow(2) * (n_.pow(2) + 1))), x_)
        },
    ));
}

fn push_rules_rule_5642(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5642,
        source: "Int[x_^2*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (n+2*(p+1)*a*x)*(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x])/(a^3*c*(n^2+4*(p+1)^2)) +
          (n^2-2*(p+1))/(a^2*c*(n^2+4*(p+1)^2)) \\[Star] Int[(c+d*x^2)^(p+1)*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && LeQ[p,-1] && NeQ[n^2-2*(p+1),0] && NeQ[n^2+4*(p+1)^2,0] &&
          Not[IntegerQ[p] && IntegerQ[I*n/2]] && Not[Not[IntegerQ[p]] && IntegerQ[(I*n-1)/2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && leq!(p_, -1)
                && neq!(n_.pow(2) - Atom::num(2) * (&p_ + 1), 0)
                && neq!(n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2), 0)
                && !(integerq!(p_) && integerq!(&i * &n_ / Atom::num(2)))
                && !(!integerq!(p_) && integerq!((&i * &n_ - Atom::num(1)) / Atom::num(2)))
        },
        rhs: {
            let denominator = n_.pow(2) + Atom::num(4) * (&p_ + 1).pow(2);
            let quadratic = &c__ + &d__ * x_.pow(2);
            let exponential = (&n_ * (&a__ * x_).acot()).exp();
            let recursive = quadratic.pow(&p_ + 1) * &exponential;
            rubi_simp(&((&n_ + Atom::num(2) * (&p_ + 1) * &a__ * x_)
                    * quadratic.pow(&p_ + 1)
                    * exponential
                    / (a__.pow(3) * &c__ * &denominator)), x_)
                    + rubi_star((n_.pow(2) - Atom::num(2) * (&p_ + 1))
                            / (a__.pow(2) * &c__ * denominator), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5643(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5643,
        source: "Int[x_^m_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p/a^(m+1) \\[Star] Subst[Int[E^(n*x)*Cot[x]^(m+2*(p+1))/Cos[x]^(2*(p+1)),x],x,ArcCot[a*x]] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && IntegerQ[m] && LeQ[3,m,-2(p+1)] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp(),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && integerq!(m_)
                && leq!(Atom::num(3), m_, -Atom::num(2) * (&p_ + 1))
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (n_ * &sub_atom).exp() * sub_atom.cot().pow(&m_ + Atom::num(2) * (&p_ + 1))
                / sub_atom.cos().pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_) / a__.pow(&m_ + 1), rubi_subst(&primitive, substitution_symbol, (&a__ * x_).acot()))
        },
    ));
}

fn push_rules_rule_5644(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5644,
        source: "Int[u_.*(c_+d_.*x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          d^p \\[Star] Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n/2]] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && integerq!(p_)
        },
        rhs: {
            let transformed = &u__
                * x_.pow(Atom::num(2) * &p_)
                * (Atom::num(1) + Atom::num(1) / (a__.pow(2) * x_.pow(2))).pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star(d__.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5645(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5645,
        source: "Int[u_.*(c_+d_.*x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (c+d*x^2)^p/(x^(2*p)*(1+1/(a^2*x^2))^p) \\[Star] Int[u*x^(2*p)*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[d,a^2*c] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(d__, a__.pow(2) * &c__)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !integerq!(p_)
        },
        rhs: {
            let reciprocal = Atom::num(1) + Atom::num(1) / (a__.pow(2) * x_.pow(2));
            let recursive = &u__
                * x_.pow(Atom::num(2) * &p_)
                * reciprocal.pow(&p_)
                * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star((&c__ + &d__ * x_.pow(2)).pow(&p_)
                    / (x_.pow(Atom::num(2) * &p_) * reciprocal.pow(&p_)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5646(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5646,
        source: "Int[u_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          c^p/(I*a)^(2*p) \\[Star] Int[u/x^(2*p)*(-1+I*a*x)^(p-I*n/2)*(1+I*a*x)^(p+I*n/2),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && IntegersQ[2*p,p+I*n/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, p_, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__, a__.pow(2) * &d__)
                && !integerq!(&i * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && integersq!([Atom::num(2) * &p_, &p_ + &i * &n_ / Atom::num(2)])
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__ * (-Atom::num(1) + &i * &a__ * x_).pow(&p_ - &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &a__ * x_).pow(&p_ + &i * &n_ / Atom::num(2))
                / x_.pow(Atom::num(2) * &p_);
            rubi_star(c__.pow(&p_) / (&i * &a__).pow(Atom::num(2) * &p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5647(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5647,
        source: "Int[(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p \\[Star] Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^2,x],x,1/x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern: (c__ + d__ / x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp(),
        with: [c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__, a__.pow(2) * &d__)
                && !integerq!(&i * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && !integersq!([Atom::num(2) * &p_, &p_ + &i * &n_ / Atom::num(2)])
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &sub_atom / &a__).pow(&p_ - &i * &n_ / Atom::num(2))
                / sub_atom.pow(2);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5648(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5648,
        source: "Int[x_^m_.*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p \\[Star] Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]] &&
          IntegerQ[m]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [m_, d__, p_, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__, a__.pow(2) * &d__)
                && !integerq!(&i * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && !integersq!([Atom::num(2) * &p_, &p_ + &i * &n_ / Atom::num(2)])
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &sub_atom / &a__).pow(&p_ - &i * &n_ / Atom::num(2))
                / sub_atom.pow(&m_ + 2);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5649(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5649,
        source: "Int[x_^m_*(c_+d_./x_^2)^p_.*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          -c^p*x^m*(1/x)^m \\[Star] Subst[Int[(1-I*x/a)^(p+I*n/2)*(1+I*x/a)^(p-I*n/2)/x^(m+2),x],x,1/x] /;
        FreeQ[{a,c,d,m,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && (IntegerQ[p] || GtQ[c,0]) && Not[IntegerQ[2*p] && IntegerQ[p+I*n/2]] &&
          Not[IntegerQ[m]]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, c__, d__, p_, n_, a__, x_],
        optional: [d__, p_, n_, a__],
        when: {
            let i = Atom::i();
            freeq!([a__, c__, d__, m_, n_, p_], x_)
                && eqq!(c__, a__.pow(2) * &d__)
                && !integerq!(&i * &n_ / Atom::num(2))
                && (integerq!(p_) || gtq!(c__, 0))
                && !integersq!([Atom::num(2) * &p_, &p_ + &i * &n_ / Atom::num(2)])
                && !integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (Atom::num(1) - &i * &sub_atom / &a__).pow(&p_ + &i * &n_ / Atom::num(2))
                * (Atom::num(1) + &i * &sub_atom / &a__).pow(&p_ - &i * &n_ / Atom::num(2))
                / sub_atom.pow(&m_ + 2);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-c__.pow(&p_) * x_.pow(&m_) * (Atom::num(1) / x_).pow(&m_), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5650(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5650,
        source: "Int[u_.*(c_+d_./x_^2)^p_*E^(n_.*ArcCot[a_.*x_]),x_Symbol] :=
          (c+d/x^2)^p/(1+1/(a^2*x^2))^p \\[Star] Int[u*(1+1/(a^2*x^2))^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,c,d,n,p},x] && EqQ[c,a^2*d] && Not[IntegerQ[I*n/2]] && Not[IntegerQ[p] || GtQ[c,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, c__, d__, p_, n_, a__, x_],
        optional: [u__, d__, n_, a__],
        when: {
            freeq!([a__, c__, d__, n_, p_], x_)
                && eqq!(c__, a__.pow(2) * &d__)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
                && !(integerq!(p_) || gtq!(c__, 0))
        },
        rhs: {
            let reciprocal = Atom::num(1) + Atom::num(1) / (a__.pow(2) * x_.pow(2));
            let recursive = &u__ * reciprocal.pow(&p_) * (&n_ * (&a__ * x_).acot()).exp();
            rubi_star((&c__ + &d__ / x_.pow(2)).pow(&p_) / reciprocal.pow(&p_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5651(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5651,
        source: "Int[u_.*E^(n_*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
          (-1)^(I*n/2) \\[Star] Int[u*E^(-n*ArcTan[c*(a+b*x)]),x] /;
        FreeQ[{a,b,c},x] && IntegerQ[I*n/2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (n_ * (c__ * (a_ + b__ * x_)).acot()).exp(),
        with: [u__, n_, c__, a_, b__, x_],
        optional: [u__, c__, b__],
        when: {
            freeq!([a_, b__, c__], x_)
                && integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let transformed = &u__ / (&n_ * (&c__ * (&a_ + &b__ * x_)).atan()).exp();
            rubi_star((-Atom::num(1)).pow(&i * &n_ / Atom::num(2)), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5652(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5652,
        source: "Int[E^(n_.*ArcCot[c_.*(a_+b_.*x_)]),x_Symbol] :=
          (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2) \\[Star]
            Int[(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
        FreeQ[{a,b,c,n},x] && Not[IntegerQ[I*n/2]]",
        desc: "Algebraic simplification and piecewise constant extraction",
        refs: [],
        pattern: (n_ * (c__ * (a_ + b__ * x_)).acot()).exp(),
        with: [n_, c__, a_, b__, x_],
        optional: [n_, c__, b__],
        when: {
            freeq!([a_, b__, c__, n_], x_)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let affine = &a_ + &b__ * x_;
            let exponent = &i * &n_ / Atom::num(2);
            let linear = Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_;
            let prefactor = (&i * &c__ * &affine).pow(&exponent)
                * (Atom::num(1) + Atom::num(1) / (&i * &c__ * &affine)).pow(&exponent)
                / linear.pow(&exponent);
            let transformed =
                linear.pow(&exponent) / (-Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_).pow(exponent);
            rubi_star(prefactor, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5653,
        source: "Int[x_^m_*E^(n_*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
          4/(I^m*n*b^(m+1)*c^(m+1)) \\[Star]
            Subst[Int[x^(2/(I*n))*(1+I*a*c+(1-I*a*c)*x^(2/(I*n)))^m/(-1+x^(2/(I*n)))^(m+2),x],x,
              (1+1/(I*c*(a+b*x)))^(I*n/2)/(1-1/(I*c*(a+b*x)))^(I*n/2)] /;
        FreeQ[{a,b,c},x] && ILtQ[m,0] && LtQ[-1,I*n,1]",
        desc: "Algebraic simplification and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (n_ * (c__ * (a_ + b__ * x_)).acoth()).exp(),
        with: [m_, n_, c__, a_, b__, x_],
        optional: [c__, b__],
        when: {
            freeq!([a_, b__, c__], x_)
                && iltq!(m_, 0)
                && ltq!(-1, Atom::i() * &n_, 1)
        },
        rhs: {
            let i = Atom::i();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let sub_power = sub_atom.pow(Atom::num(2) / (&i * &n_));
            let payload = &sub_power
                * (Atom::num(1) + &i * &a_ * &c__ + (Atom::num(1) - &i * &a_ * &c__) * &sub_power).pow(&m_)
                / (-Atom::num(1) + sub_power).pow(&m_ + 2);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let affine = &a_ + &b__ * x_;
            let substitution = (Atom::num(1) + Atom::num(1) / (&i * &c__ * &affine)).pow(&i * &n_ / Atom::num(2))
                / (Atom::num(1) - Atom::num(1) / (&i * &c__ * &affine)).pow(&i * &n_ / Atom::num(2));
            rubi_star(Atom::num(4)
                    / (i.pow(&m_) * &n_ * b__.pow(&m_ + 1) * c__.pow(&m_ + 1)), rubi_subst(&primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_5654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5654,
        source: "Int[(d_.+e_.*x_)^m_.*E^(n_.*ArcCoth[c_.*(a_+b_.*x_)]),x_Symbol] :=
          (I*c*(a+b*x))^(I*n/2)*(1+1/(I*c*(a+b*x)))^(I*n/2)/(1+I*a*c+I*b*c*x)^(I*n/2) \\[Star]
            Int[(d+e*x)^m*(1+I*a*c+I*b*c*x)^(I*n/2)/(-1+I*a*c+I*b*c*x)^(I*n/2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[I*n/2]]",
        desc: "Algebraic simplification and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (n_ * (c__ * (a_ + b__ * x_)).acoth()).exp(),
        with: [d__, e__, m_, n_, c__, a_, b__, x_],
        optional: [d__, e__, m_, n_, c__, b__],
        when: {
            freeq!([a_, b__, c__, d__, e__, m_, n_], x_)
                && !integerq!(Atom::i() * &n_ / Atom::num(2))
        },
        rhs: {
            let i = Atom::i();
            let affine = &a_ + &b__ * x_;
            let exponent = &i * &n_ / Atom::num(2);
            let linear = Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_;
            let prefactor = (&i * &c__ * &affine).pow(&exponent)
                * (Atom::num(1) + Atom::num(1) / (&i * &c__ * &affine)).pow(&exponent)
                / linear.pow(&exponent);
            let transformed = (&d__ + &e__ * x_).pow(&m_) * linear.pow(&exponent)
                / (-Atom::num(1) + &i * &a_ * &c__ + &i * &b__ * &c__ * x_).pow(exponent);
            rubi_star(prefactor, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c__, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5655,
        source: "Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
          (c/(1+a^2))^p*((I*a+I*b*x)/(1+I*a+I*b*x))^(I*n/2)*((1+I*a+I*b*x)/(I*a+I*b*x))^(I*n/2)*
            ((1-I*a-I*b*x)^(I*n/2)/(-1+I*a+I*b*x)^(I*n/2)) \\[Star]
            Int[u*(1-I*a-I*b*x)^(p-I*n/2)*(1+I*a+I*b*x)^(p+I*n/2),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c-e(1+a^2),0] && (IntegerQ[p] || GtQ[c/(1+a^2),0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, c__, d__, e__, p_, n_, a_, b__, x_],
        optional: [u__, d__, e__, p_, n_, b__],
        when: {
            let i = Atom::i();
            freeq!([a_, b__, c__, d__, e__, n_, p_], x_)
                && !integerq!(&i * &n_ / Atom::num(2))
                && eqq!(&b__ * &d__ - Atom::num(2) * &a_ * &e__, 0)
                && eqq!(b__.pow(2) * &c__ - &e__ * (Atom::num(1) + a_.pow(2)), 0)
                && (integerq!(p_) || gtq!(&c__ / (Atom::num(1) + a_.pow(2)), 0))
        },
        rhs: {
            let i = Atom::i();
            let exponent = &i * &n_ / Atom::num(2);
            let i_affine = &i * &a_ + &i * &b__ * x_;
            let plus_linear = Atom::num(1) + &i * &a_ + &i * &b__ * x_;
            let minus_linear = Atom::num(1) - &i * &a_ - &i * &b__ * x_;
            let shifted_linear = -Atom::num(1) + &i * &a_ + &i * &b__ * x_;
            let prefactor = (&c__ / (Atom::num(1) + a_.pow(2))).pow(&p_)
                * (&i_affine / &plus_linear).pow(&exponent)
                * (&plus_linear / i_affine).pow(&exponent)
                * minus_linear.pow(&exponent)
                / shifted_linear.pow(&exponent);
            let transformed = &u__
                * minus_linear.pow(&p_ - &exponent)
                * plus_linear.pow(&p_ + exponent);
            rubi_star(prefactor, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c__, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5656,
        source: "Int[u_.*(c_+d_.*x_+e_.*x_^2)^p_.*E^(n_.*ArcCot[a_+b_.*x_]),x_Symbol] :=
          (c+d*x+e*x^2)^p/(1+a^2+2*a*b*x+b^2*x^2)^p \\[Star] Int[u*(1+a^2+2*a*b*x+b^2*x^2)^p*E^(n*ArcCot[a*x]),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[I*n/2]] && EqQ[b*d-2*a*e,0] && EqQ[b^2*c-e(1+a^2),0] && Not[IntegerQ[p] || GtQ[c/(1+a^2),0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, c__, d__, e__, p_, n_, a_, b__, x_],
        optional: [u__, d__, e__, p_, n_, b__],
        when: {
            let i = Atom::i();
            freeq!([a_, b__, c__, d__, e__, n_, p_], x_)
                && !integerq!(&i * &n_ / Atom::num(2))
                && eqq!(&b__ * &d__ - Atom::num(2) * &a_ * &e__, 0)
                && eqq!(b__.pow(2) * &c__ - &e__ * (Atom::num(1) + a_.pow(2)), 0)
                && !(integerq!(p_) || gtq!(&c__ / (Atom::num(1) + a_.pow(2)), 0))
        },
        rhs: {
            let denominator = Atom::num(1)
                + a_.pow(2)
                + Atom::num(2) * &a_ * &b__ * x_
                + b__.pow(2) * x_.pow(2);
            let transformed = &u__ * denominator.pow(&p_) * (&n_ * (&a_ * x_).acot()).exp();
            rubi_star((&c__ + &d__ * x_ + &e__ * x_.pow(2)).pow(&p_)
                    / denominator.pow(&p_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5657,
        source: "Int[u_.*E^(n_.*ArcCot[c_./(a_.+b_.*x_)]),x_Symbol] :=
          Int[u*E^(n*ArcTan[a/c+b*x/c]),x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (n_ * (c__ / (a__ + b__ * x_)).acot()).exp(),
        with: [u__, n_, c__, a__, b__, x_],
        optional: [u__, n_, c__, a__, b__],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let transformed = &u__ * (&n_ * (&a__ / &c__ + &b__ * x_ / &c__).atan()).exp();
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5593_through_5642_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5593..=5642).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5593..=5642).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5593_through_5642_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5593..=5642).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5593..=5642).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5643_through_5657_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5643..=5657).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5643..=5657).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5643_through_5692_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5643..=5692).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5643..=5692).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n__ = symbols.n__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(2)).pow(p_) * (n__ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ / x_).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let n__ = symbols.n__;
    let x_ = symbols.x_;
    (n__ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a_ = symbols.a_;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_ + e__ * x_.pow(2)).pow(p_) * (n_ * (a_ + b__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a_ = symbols.a_;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_ + e__ * x_.pow(2)).pow(p_) * (n_ * (a_ + b__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ / x_).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ / x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (c__ + d__ / x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(2) * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_.pow(2)).pow(p_) * (n_ * (a__ * x_).atan()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ / x_).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ / x_.pow(2)).pow(p_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (n_ * (a__ * x_).acot()).exp()
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let m_ = symbols.m_;
    let n__ = symbols.n__;
    let x_ = symbols.x_;
    x_.pow(m_) * (n__ * (a__ * x_).atan()).exp()
}
