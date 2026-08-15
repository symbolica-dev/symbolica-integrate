use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5379(rules);
    push_rules_rule_5380(rules);
    push_rules_rule_5381(rules);
    push_rules_rule_5382(rules);
    push_rules_rule_5383(rules);
    push_rules_rule_5384(rules);
    push_rules_rule_5385(rules);
    push_rules_rule_5386(rules);
    push_rules_rule_5387(rules);
    push_rules_rule_5388(rules);
    push_rules_rule_5389(rules);
    push_rules_rule_5390(rules);
    push_rules_rule_5391(rules);
    push_rules_rule_5392(rules);
    push_rules_rule_5393(rules);
    push_rules_rule_5394(rules);
    push_rules_rule_5395(rules);
    push_rules_rule_5396(rules);
    push_rules_rule_5397(rules);
    push_rules_rule_5398(rules);
    push_rules_rule_5399(rules);
    push_rules_rule_5400(rules);
}

fn push_rules_rule_5379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5379,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTan[c*x])^p*Log[2/(1+e*x/d)]/e +
          b*c*p/e \\[Star] Int[(a+b*ArcTan[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let logarithm = (Atom::num(2) / (Atom::num(1) + &e__ * x_ / &d__)).log();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &logarithm
                / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(-argument.pow(&p_) * logarithm / &e__), x_)
                    + rubi_star(&b__ * &c__ * &p_ / &e__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5380,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCot[c*x])^p*Log[2/(1+e*x/d)]/e -
          b*c*p/e \\[Star] Int[(a+b*ArcCot[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2+e^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let logarithm = (Atom::num(2) / (Atom::num(1) + &e__ * x_ / &d__)).log();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &logarithm
                / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(-argument.pow(&p_) * logarithm / &e__), x_)
                    - rubi_star(&b__ * &c__ * &p_ / &e__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5381,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTan[c*x])*Log[2/(1-I*c*x)]/e +
          b*c/e \\[Star] Int[Log[2/(1-I*c*x)]/(1+c^2*x^2),x] +
          (a+b*ArcTan[c*x])*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e -
          b*c/e \\[Star] Int[Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let log1 = (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log();
            let log2 = (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                .log();
            let denom = Atom::num(1) + c__.pow(2) * x_.pow(2);
            rubi_simp(&(-&argument * &log1 / &e__), x_)
                    + rubi_star(&b__ * &c__ / &e__, rubi_rhs_int(&(log1 / &denom), x_))
                    + rubi_simp(&(argument * &log2 / &e__), x_)
                    - rubi_star(&b__ * &c__ / &e__, rubi_rhs_int(&(log2 / denom), x_))
        },
    ));
}

fn push_rules_rule_5382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5382,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCot[c*x])*Log[2/(1-I*c*x)]/e -
          b*c/e \\[Star] Int[Log[2/(1-I*c*x)]/(1+c^2*x^2),x] +
          (a+b*ArcCot[c*x])*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e +
          b*c/e \\[Star] Int[Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let log1 = (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log();
            let log2 = (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                .log();
            let denom = Atom::num(1) + c__.pow(2) * x_.pow(2);
            rubi_simp(&(-&argument * &log1 / &e__), x_)
                    - rubi_star(&b__ * &c__ / &e__, rubi_rhs_int(&(log1 / &denom), x_))
                    + rubi_simp(&(argument * &log2 / &e__), x_)
                    + rubi_star(&b__ * &c__ / &e__, rubi_rhs_int(&(log2 / denom), x_))
        },
    ));
}

fn push_rules_rule_5383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5383,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTan[c*x])^2*Log[2/(1-I*c*x)]/e +
          I*b*(a+b*ArcTan[c*x])*PolyLog[2,1-2/(1-I*c*x)]/e -
          b^2*PolyLog[3,1-2/(1-I*c*x)]/(2*e) +
          (a+b*ArcTan[c*x])^2*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e -
          I*b*(a+b*ArcTan[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e +
          b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()).pow(2) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) - &i * &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_));
            let simp = |term: Atom| rubi_simp(&term, x_);
            simp(-argument.pow(2)
                    * (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log()
                    / &e__)
                    + simp(&i * &b__ * &argument * &z1.polylog(2) / &e__)
                    - simp(b__.pow(2) * z1.polylog(3) / (Atom::num(2) * &e__))
                    + simp(argument.pow(2)
                        * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                            / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                            .log()
                        / &e__)
                    - simp(&i * &b__ * argument * &z2.polylog(2) / &e__)
                    + simp(b__.pow(2) * z2.polylog(3) / (Atom::num(2) * e__))
        },
    ));
}

fn push_rules_rule_5384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5384,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCot[c*x])^2*Log[2/(1-I*c*x)]/e -
          I*b*(a+b*ArcCot[c*x])*PolyLog[2,1-2/(1-I*c*x)]/e -
          b^2*PolyLog[3,1-2/(1-I*c*x)]/(2*e) +
          (a+b*ArcCot[c*x])^2*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e +
          I*b*(a+b*ArcCot[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e +
          b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()).pow(2) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) - &i * &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_));
            let simp = |term: Atom| rubi_simp(&term, x_);
            simp(-argument.pow(2)
                    * (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log()
                    / &e__)
                    - simp(&i * &b__ * &argument * &z1.polylog(2) / &e__)
                    - simp(b__.pow(2) * z1.polylog(3) / (Atom::num(2) * &e__))
                    + simp(argument.pow(2)
                        * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                            / ((&c__ * &d__ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                            .log()
                        / &e__)
                    + simp(&i * &b__ * argument * &z2.polylog(2) / &e__)
                    + simp(b__.pow(2) * z2.polylog(3) / (Atom::num(2) * e__))
        },
    ));
}

fn push_rules_rule_5385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, x_);
    rules.push(rubi_rule!(
        order: 5385,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTan[c*x])^3*Log[2/(1-I*c*x)]/e +
          3*I*b*(a+b*ArcTan[c*x])^2*PolyLog[2,1-2/(1-I*c*x)]/(2*e) -
          3*b^2*(a+b*ArcTan[c*x])*PolyLog[3,1-2/(1-I*c*x)]/(2*e) -
          3*I*b^3*PolyLog[4,1-2/(1-I*c*x)]/(4*e) +
          (a+b*ArcTan[c*x])^3*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e -
          3*I*b*(a+b*ArcTan[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) +
          3*b^2*(a+b*ArcTan[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) +
          3*I*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(4*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()).pow(3) / (d_ + e__ * x_),
        with: [a__, b__, c__, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d_, e__], x_)
                && neq!(c__.pow(2) * d_.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) - &i * &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d_ + &e__ * x_)
                    / ((&c__ * &d_ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_));
            let simp = |term: Atom| rubi_simp(&term, x_);

            simp(-argument.pow(3)
                    * (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log()
                    / &e__)
                    + simp(Atom::num(3) * &i * &b__ * argument.pow(2) * &z1.polylog(2) / (Atom::num(2) * &e__))
                    - simp(Atom::num(3) * b__.pow(2) * &argument * &z1.polylog(3) / (Atom::num(2) * &e__))
                    - simp(Atom::num(3) * &i * b__.pow(3) * z1.polylog(4) / (Atom::num(4) * &e__))
                    + simp(argument.pow(3)
                        * (Atom::num(2) * &c__ * (&d_ + &e__ * x_)
                            / ((&c__ * &d_ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                            .log()
                        / &e__)
                    - simp(Atom::num(3) * &i * &b__ * argument.pow(2) * &z2.polylog(2) / (Atom::num(2) * &e__))
                    + simp(Atom::num(3) * b__.pow(2) * argument * &z2.polylog(3) / (Atom::num(2) * &e__))
                    + simp(Atom::num(3) * i * b__.pow(3) * z2.polylog(4) / (Atom::num(4) * e__))
        },
    ));
}

fn push_rules_rule_5386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, x_);
    rules.push(rubi_rule!(
        order: 5386,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCot[c*x])^3*Log[2/(1-I*c*x)]/e -
          3*I*b*(a+b*ArcCot[c*x])^2*PolyLog[2,1-2/(1-I*c*x)]/(2*e) -
          3*b^2*(a+b*ArcCot[c*x])*PolyLog[3,1-2/(1-I*c*x)]/(2*e) +
          3*I*b^3*PolyLog[4,1-2/(1-I*c*x)]/(4*e) +
          (a+b*ArcCot[c*x])^3*Log[2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/e +
          3*I*b*(a+b*ArcCot[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) +
          3*b^2*(a+b*ArcCot[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(2*e) -
          3*I*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+I*e)*(1-I*c*x))]/(4*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2+e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()).pow(3) / (d_ + e__ * x_),
        with: [a__, b__, c__, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d_, e__], x_)
                && neq!(c__.pow(2) * d_.pow(2) + e__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) - &i * &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d_ + &e__ * x_)
                    / ((&c__ * &d_ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_));
            let simp = |term: Atom| rubi_simp(&term, x_);

            simp(-argument.pow(3)
                    * (Atom::num(2) / (Atom::num(1) - &i * &c__ * x_)).log()
                    / &e__)
                    - simp(Atom::num(3) * &i * &b__ * argument.pow(2) * &z1.polylog(2) / (Atom::num(2) * &e__))
                    - simp(Atom::num(3) * b__.pow(2) * &argument * &z1.polylog(3) / (Atom::num(2) * &e__))
                    + simp(Atom::num(3) * &i * b__.pow(3) * z1.polylog(4) / (Atom::num(4) * &e__))
                    + simp(argument.pow(3)
                        * (Atom::num(2) * &c__ * (&d_ + &e__ * x_)
                            / ((&c__ * &d_ + &i * &e__) * (Atom::num(1) - &i * &c__ * x_)))
                            .log()
                        / &e__)
                    + simp(Atom::num(3) * &i * &b__ * argument.pow(2) * &z2.polylog(2) / (Atom::num(2) * &e__))
                    + simp(Atom::num(3) * b__.pow(2) * argument * &z2.polylog(3) / (Atom::num(2) * &e__))
                    - simp(Atom::num(3) * i * b__.pow(3) * z2.polylog(4) / (Atom::num(4) * e__))
        },
    ));
}

fn push_rules_rule_5387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 5387,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_]),x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcTan[c*x])/(e*(q+1)) -
          b*c/(e*(q+1)) \\[Star] Int[(d+e*x)^(q+1)/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).atan()),
        with: [d_, e__, q_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, q_],
        when: { freeq!([a__, b__, c__, d_, e__, q_], x_) && neq!(q_, -1) },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let recursive = linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (&e__ * (&q_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 5388,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_]),x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcCot[c*x])/(e*(q+1)) +
          b*c/(e*(q+1)) \\[Star] Int[(d+e*x)^(q+1)/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).acot()),
        with: [d_, e__, q_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, q_],
        when: { freeq!([a__, b__, c__, d_, e__, q_], x_) && neq!(q_, -1) },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let recursive = linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument / (&e__ * (&q_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ / (&e__ * (&q_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5389,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTan[c_.*x_])^p_,x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcTan[c*x])^p/(e*(q+1)) -
          b*c*p/(e*(q+1)) \\[Star] Int[ExpandIntegrand[(a+b*ArcTan[c*x])^(p-1),(d+e*x)^(q+1)/(1+c^2*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).atan()).pow(p_),
        with: [d_, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, a__, b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, d_, e__], x_)
                && igtq!(p_, 1)
                && integerq!(q_)
                && neq!(q_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let linear = &d_ + &e__ * x_;
            let expanded = rubi_expand_integrand_product(
                &argument.pow(&p_ - Atom::num(1)),
                &(linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) + c__.pow(2) * x_.pow(2))),
                x_,
            );
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument.pow(&p_) / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &p_ / (&e__ * (&q_ + Atom::num(1))), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_5390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5390,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCot[c_.*x_])^p_,x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcCot[c*x])^p/(e*(q+1)) +
          b*c*p/(e*(q+1)) \\[Star] Int[ExpandIntegrand[(a+b*ArcCot[c*x])^(p-1),(d+e*x)^(q+1)/(1+c^2*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).acot()).pow(p_),
        with: [d_, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, a__, b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, d_, e__], x_)
                && igtq!(p_, 1)
                && integerq!(q_)
                && neq!(q_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let linear = &d_ + &e__ * x_;
            let expanded = rubi_expand_integrand_product(
                &argument.pow(&p_ - Atom::num(1)),
                &(linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) + c__.pow(2) * x_.pow(2))),
                x_,
            );
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument.pow(&p_) / (&e__ * (&q_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &p_ / (&e__ * (&q_ + Atom::num(1))), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_5391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5391,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          Log[d+e*x]*(a+b*ArcTan[c*x^n])/e -
          b*c*n/e \\[Star] Int[x^(n-1)*Log[d+e*x]/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d_, e__, n_], x_) && integerq!(n_) },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = x_.pow(&n_ - Atom::num(1)) * &linear.log()
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(linear.log() * argument / &e__), x_)
                    - rubi_star(&b__ * &c__ * &n_ / &e__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5392,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          Log[d+e*x]*(a+b*ArcCot[c*x^n])/e +
          b*c*n/e \\[Star] Int[x^(n-1)*Log[d+e*x]/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d_, e__, n_], x_) && integerq!(n_) },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = x_.pow(&n_ - Atom::num(1)) * &linear.log()
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(linear.log() * argument / &e__), x_)
                    + rubi_star(&b__ * &c__ * &n_ / &e__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5393,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcTan[c*x^(k*n)])/(d+e*x^k),x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d_, e__], x_) && fractionq!(n_) },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atan())
                / (&d_ + &e__ * sub_atom.pow(&k));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d_, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5394,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcCot[c*x^(k*n)])/(d+e*x^k),x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d_, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d_, e__], x_) && fractionq!(n_) },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acot())
                / (&d_ + &e__ * sub_atom.pow(&k));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5395,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcTan[c*x^n])/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[x^(n-1)*(d+e*x)^(m+1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()),
        with: [d_, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d_, e__, m_, n_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = x_.pow(&n_ - Atom::num(1)) * linear.pow(&m_ + Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&e__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5396,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCot[c*x^n])/(e*(m+1)) +
          b*c*n/(e*(m+1)) \\[Star] Int[x^(n-1)*(d+e*x)^(m+1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()),
        with: [d_, e__, m_, a__, b__, c__, n_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d_, e__, m_, n_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d_ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = x_.pow(&n_ - Atom::num(1)) * linear.pow(&m_ + Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&e__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5397,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcTan[c*x^n])^p,(d+e*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,1] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d_ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_),
        with: [d_, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d_, e__, n_], x_)
                && igtq!(p_, 1)
                && igtq!(m_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_.pow(&n_)).atan()).pow(&p_),
                &(&d_ + &e__ * x_).pow(&m_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5398,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCot[c*x^n])^p,(d+e*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,1] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d_ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_),
        with: [d_, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d_, e__, n_], x_)
                && igtq!(p_, 1)
                && igtq!(m_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_.pow(&n_)).acot()).pow(&p_),
                &(&d_ + &e__ * x_).pow(&m_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5399,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(a+b*ArcTan[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable((&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).atan()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_5400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5400,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(a+b*ArcCot[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable((&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).acot()).pow(&p_), x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5379_through_5392_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5379..=5392).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5379..=5392).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5343_through_5392_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5343..=5392).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5343..=5392).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5393_through_5400_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5393..=5400).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5393..=5400).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5381_and_5382_match_composite_affine_constants() {
        let x = symbol!("x");
        for (integrand, specific, generic) in [
            ("(a+b*atan(c+d*x))^2/(e+f*x)^2", 5381, 5399),
            ("(a+b*acot(c+d*x))^2/(e+f*x)^2", 5382, 5400),
            ("(a+b*atan(c+d*x))^3/(e+f*x)^2", 5383, 5399),
            ("(a+b*acot(c+d*x))^3/(e+f*x)^2", 5384, 5400),
        ] {
            assert!(
                parse!(integrand).integrate(x).is_ok(),
                "DownValue {specific} must run before generic DownValue {generic}"
            );
        }
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).acot()) / (d_ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d_ = symbols.d_;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).atan()) / (d_ + e__ * x_)
}
