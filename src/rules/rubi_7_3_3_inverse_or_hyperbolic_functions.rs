use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6470(rules);
    push_rules_rule_6471(rules);
    push_rules_rule_6472(rules);
    push_rules_rule_6473(rules);
    push_rules_rule_6474(rules);
    push_rules_rule_6475(rules);
    push_rules_rule_6476(rules);
    push_rules_rule_6477(rules);
    push_rules_rule_6478(rules);
    push_rules_rule_6479(rules);
    push_rules_rule_6480(rules);
    push_rules_rule_6481(rules);
    push_rules_rule_6482(rules);
    push_rules_rule_6483(rules);
    push_rules_rule_6484(rules);
    push_rules_rule_6485(rules);
    push_rules_rule_6486(rules);
    push_rules_rule_6487(rules);
    push_rules_rule_6488(rules);
    push_rules_rule_6489(rules);
    push_rules_rule_6490(rules);
    push_rules_rule_6491(rules);
}

fn push_rules_rule_6470(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6470,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTanh[c*x])^p*Log[2/(1+e*x/d)]/e +
          b*c*p/e \\[Star] Int[(a+b*ArcTanh[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let explicit_logarithm = Atom::num(2) / (Atom::num(1) + &e__ * x_ / &d__);
            let polylog_argument = Atom::num(1) - &explicit_logarithm;
            let logarithm = (Atom::num(1) - polylog_argument).log();
            let recursive = argument.pow(&p_ - Atom::num(1)) * explicit_logarithm.log()
                / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(-argument.pow(&p_) * logarithm / &e__), x_)
                    + rubi_star(&b__ * &c__ * &p_ / &e__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6471(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6471,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])^p_./(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCoth[c*x])^p*Log[2/(1+e*x/d)]/e +
          b*c*p/e \\[Star] Int[(a+b*ArcCoth[c*x])^(p-1)*Log[2/(1+e*x/d)]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && EqQ[c^2*d^2-e^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let explicit_logarithm = Atom::num(2) / (Atom::num(1) + &e__ * x_ / &d__);
            let polylog_argument = Atom::num(1) - &explicit_logarithm;
            let logarithm = (Atom::num(1) - polylog_argument).log();
            let recursive = argument.pow(&p_ - Atom::num(1)) * explicit_logarithm.log()
                / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(-argument.pow(&p_) * logarithm / &e__), x_)
                    + rubi_star(&b__ * &c__ * &p_ / &e__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6472(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6472,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTanh[c*x])*Log[2/(1+c*x)]/e +
          b*c/e \\[Star] Int[Log[2/(1+c*x)]/(1-c^2*x^2),x] +
          (a+b*ArcTanh[c*x])*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b*c/e \\[Star] Int[Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let log1 = (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log();
            let log2 = (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                .log();
            let denom = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let first_primitive = rubi_rhs_int(&(&log1 / &denom), x_);
            let second_primitive = rubi_rhs_int(&(&log2 / denom), x_);
            rubi_simp(&(-&argument * &log1 / &e__), x_)
                    + rubi_star(&b__ * &c__ / &e__, first_primitive)
                    + rubi_simp(&(argument * &log2 / &e__), x_)
                    - rubi_star(&b__ * &c__ / &e__, second_primitive)
        },
    ));
}

fn push_rules_rule_6473(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6473,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCoth[c*x])*Log[2/(1+c*x)]/e +
          b*c/e \\[Star] Int[Log[2/(1+c*x)]/(1-c^2*x^2),x] +
          (a+b*ArcCoth[c*x])*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b*c/e \\[Star] Int[Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let log1 = (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log();
            let log2 = (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                .log();
            let denom = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let first_primitive = rubi_rhs_int(&(&log1 / &denom), x_);
            let second_primitive = rubi_rhs_int(&(&log2 / denom), x_);
            rubi_simp(&(-&argument * &log1 / &e__), x_)
                    + rubi_star(&b__ * &c__ / &e__, first_primitive)
                    + rubi_simp(&(argument * &log2 / &e__), x_)
                    - rubi_star(&b__ * &c__ / &e__, second_primitive)
        },
    ));
}

fn push_rules_rule_6474(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6474,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTanh[c*x])^2*Log[2/(1+c*x)]/e +
          b*(a+b*ArcTanh[c*x])*PolyLog[2,1-2/(1+c*x)]/e +
          b^2*PolyLog[3,1-2/(1+c*x)]/(2*e) +
          (a+b*ArcTanh[c*x])^2*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b*(a+b*ArcTanh[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()).pow(2) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) + &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_));
            let first_log = rubi_simp(
                &(-argument.pow(2)
                    * (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log()
                    / &e__),
                x_,
            );
            let first_dilog = rubi_simp(
                &(&b__ * &argument * &z1.polylog(2) / &e__),
                x_,
            );
            let first_trilog =
                rubi_simp(&(b__.pow(2) * z1.polylog(3) / (Atom::num(2) * &e__)), x_);
            let second_log = rubi_simp(
                &(argument.pow(2)
                    * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                        / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                        .log()
                    / &e__),
                x_,
            );
            let second_dilog =
                rubi_simp(&(&b__ * argument * &z2.polylog(2) / &e__), x_);
            let second_trilog =
                rubi_simp(&(b__.pow(2) * z2.polylog(3) / (Atom::num(2) * e__)), x_);

            rubi_simp(&(first_log), x_) + rubi_simp(&(first_dilog), x_) + rubi_simp(&(first_trilog), x_) + rubi_simp(&(second_log), x_) - rubi_simp(&(second_dilog), x_) - rubi_simp(&(second_trilog), x_)
        },
    ));
}

fn push_rules_rule_6475(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6475,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])^2/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCoth[c*x])^2*Log[2/(1+c*x)]/e +
          b*(a+b*ArcCoth[c*x])*PolyLog[2,1-2/(1+c*x)]/e +
          b^2*PolyLog[3,1-2/(1+c*x)]/(2*e) +
          (a+b*ArcCoth[c*x])^2*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b*(a+b*ArcCoth[c*x])*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          b^2*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()).pow(2) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) + &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_));
            let first_log = rubi_simp(
                &(-argument.pow(2)
                    * (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log()
                    / &e__),
                x_,
            );
            let first_dilog = rubi_simp(
                &(&b__ * &argument * &z1.polylog(2) / &e__),
                x_,
            );
            let first_trilog =
                rubi_simp(&(b__.pow(2) * z1.polylog(3) / (Atom::num(2) * &e__)), x_);
            let second_log = rubi_simp(
                &(argument.pow(2)
                    * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                        / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                        .log()
                    / &e__),
                x_,
            );
            let second_dilog =
                rubi_simp(&(&b__ * argument * &z2.polylog(2) / &e__), x_);
            let second_trilog =
                rubi_simp(&(b__.pow(2) * z2.polylog(3) / (Atom::num(2) * e__)), x_);

            rubi_simp(&(first_log), x_) + rubi_simp(&(first_dilog), x_) + rubi_simp(&(first_trilog), x_) + rubi_simp(&(second_log), x_) - rubi_simp(&(second_dilog), x_) - rubi_simp(&(second_trilog), x_)
        },
    ));
}

fn push_rules_rule_6476(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6476,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcTanh[c*x])^3*Log[2/(1+c*x)]/e +
          3*b*(a+b*ArcTanh[c*x])^2*PolyLog[2,1-2/(1+c*x)]/(2*e) +
          3*b^2*(a+b*ArcTanh[c*x])*PolyLog[3,1-2/(1+c*x)]/(2*e) +
          3*b^3*PolyLog[4,1-2/(1+c*x)]/(4*e) +
          (a+b*ArcTanh[c*x])^3*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          3*b*(a+b*ArcTanh[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) -
          3*b^2*(a+b*ArcTanh[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) -
          3*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(4*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()).pow(3) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) + &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_));

            let first_log = rubi_simp(
                &(-argument.pow(3)
                    * (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log()
                    / &e__),
                x_,
            );
            let first_dilog = rubi_simp(
                &(Atom::num(3) * &b__ * argument.pow(2) * &z1.polylog(2)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let first_trilog = rubi_simp(
                &(Atom::num(3) * b__.pow(2) * &argument * &z1.polylog(3)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let first_polylog4 = rubi_simp(
                &(Atom::num(3) * b__.pow(3) * z1.polylog(4) / (Atom::num(4) * &e__)),
                x_,
            );
            let second_log = rubi_simp(
                &(argument.pow(3)
                    * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                        / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                        .log()
                    / &e__),
                x_,
            );
            let second_dilog = rubi_simp(
                &(Atom::num(3) * &b__ * argument.pow(2) * &z2.polylog(2)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let second_trilog = rubi_simp(
                &(Atom::num(3) * b__.pow(2) * argument * &z2.polylog(3)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let second_polylog4 = rubi_simp(
                &(Atom::num(3) * b__.pow(3) * z2.polylog(4) / (Atom::num(4) * e__)),
                x_,
            );

            rubi_simp(&(first_log), x_) + rubi_simp(&(first_dilog), x_) + rubi_simp(&(first_trilog), x_) + rubi_simp(&(first_polylog4), x_) + rubi_simp(&(second_log), x_)
                    - rubi_simp(&(second_dilog), x_)
                    - rubi_simp(&(second_trilog), x_)
                    - rubi_simp(&(second_polylog4), x_)
        },
    ));
}

fn push_rules_rule_6477(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6477,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])^3/(d_+e_.*x_),x_Symbol] :=
          -(a+b*ArcCoth[c*x])^3*Log[2/(1+c*x)]/e +
          3*b*(a+b*ArcCoth[c*x])^2*PolyLog[2,1-2/(1+c*x)]/(2*e) +
          3*b^2*(a+b*ArcCoth[c*x])*PolyLog[3,1-2/(1+c*x)]/(2*e) +
          3*b^3*PolyLog[4,1-2/(1+c*x)]/(4*e) +
          (a+b*ArcCoth[c*x])^3*Log[2*c*(d+e*x)/((c*d+e)*(1+c*x))]/e -
          3*b*(a+b*ArcCoth[c*x])^2*PolyLog[2,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) -
          3*b^2*(a+b*ArcCoth[c*x])*PolyLog[3,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(2*e) -
          3*b^3*PolyLog[4,1-2*c*(d+e*x)/((c*d+e)*(1+c*x))]/(4*e) /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d^2-e^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()).pow(3) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let z1 = Atom::num(1) - Atom::num(2) / (Atom::num(1) + &c__ * x_);
            let z2 = Atom::num(1)
                - Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                    / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_));

            let first_log = rubi_simp(
                &(-argument.pow(3)
                    * (Atom::num(2) / (Atom::num(1) + &c__ * x_)).log()
                    / &e__),
                x_,
            );
            let first_dilog = rubi_simp(
                &(Atom::num(3) * &b__ * argument.pow(2) * &z1.polylog(2)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let first_trilog = rubi_simp(
                &(Atom::num(3) * b__.pow(2) * &argument * &z1.polylog(3)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let first_polylog4 = rubi_simp(
                &(Atom::num(3) * b__.pow(3) * z1.polylog(4) / (Atom::num(4) * &e__)),
                x_,
            );
            let second_log = rubi_simp(
                &(argument.pow(3)
                    * (Atom::num(2) * &c__ * (&d__ + &e__ * x_)
                        / ((&c__ * &d__ + &e__) * (Atom::num(1) + &c__ * x_)))
                        .log()
                    / &e__),
                x_,
            );
            let second_dilog = rubi_simp(
                &(Atom::num(3) * &b__ * argument.pow(2) * &z2.polylog(2)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let second_trilog = rubi_simp(
                &(Atom::num(3) * b__.pow(2) * argument * &z2.polylog(3)
                    / (Atom::num(2) * &e__)),
                x_,
            );
            let second_polylog4 = rubi_simp(
                &(Atom::num(3) * b__.pow(3) * z2.polylog(4) / (Atom::num(4) * e__)),
                x_,
            );

            rubi_simp(&(first_log), x_) + rubi_simp(&(first_dilog), x_) + rubi_simp(&(first_trilog), x_) + rubi_simp(&(first_polylog4), x_) + rubi_simp(&(second_log), x_)
                    - rubi_simp(&(second_dilog), x_)
                    - rubi_simp(&(second_trilog), x_)
                    - rubi_simp(&(second_polylog4), x_)
        },
    ));
}

fn push_rules_rule_6478(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 6478,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_]),x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcTanh[c*x])/(e*(q+1)) -
          b*c/(e*(q+1)) \\[Star] Int[(d+e*x)^(q+1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).atanh()),
        with: [d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, q_],
        when: { freeq!([a__, b__, c__, d__, e__, q_], x_) && neq!(q_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let recursive = linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument
                    / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (&e__ * (&q_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6479(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 6479,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_]),x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcCoth[c*x])/(e*(q+1)) -
          b*c/(e*(q+1)) \\[Star] Int[(d+e*x)^(q+1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).acoth()),
        with: [d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, q_],
        when: { freeq!([a__, b__, c__, d__, e__, q_], x_) && neq!(q_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let recursive = linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument
                    / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (&e__ * (&q_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6480(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6480,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcTanh[c_.*x_])^p_,x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcTanh[c*x])^p/(e*(q+1)) -
          b*c*p/(e*(q+1)) \\[Star] Int[ExpandIntegrand[(a+b*ArcTanh[c*x])^(p-1),(d+e*x)^(q+1)/(1-c^2*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).atanh()).pow(p_),
        with: [d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, a__, b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 1)
                && integerq!(q_)
                && neq!(q_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let linear = &d__ + &e__ * x_;
            let expanded = rubi_expand_integrand_product(
                &argument.pow(&p_ - Atom::num(1)),
                &(linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2))),
                x_,
            );
            let recursive_primitive = rubi_rhs_int(&expanded, x_);
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument.pow(&p_)
                    / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &p_ / (&e__ * (&q_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6481(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6481,
        source: "Int[(d_+e_.*x_)^q_.*(a_.+b_.*ArcCoth[c_.*x_])^p_,x_Symbol] :=
          (d+e*x)^(q+1)*(a+b*ArcCoth[c*x])^p/(e*(q+1)) -
          b*c*p/(e*(q+1)) \\[Star] Int[ExpandIntegrand[(a+b*ArcCoth[c*x])^(p-1),(d+e*x)^(q+1)/(1-c^2*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,1] && IntegerQ[q] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).acoth()).pow(p_),
        with: [d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, a__, b__, c__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 1)
                && integerq!(q_)
                && neq!(q_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let linear = &d__ + &e__ * x_;
            let expanded = rubi_expand_integrand_product(
                &argument.pow(&p_ - Atom::num(1)),
                &(linear.pow(&q_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2))),
                x_,
            );
            let recursive_primitive = rubi_rhs_int(&expanded, x_);
            rubi_simp(&(linear.pow(&q_ + Atom::num(1)) * argument.pow(&p_)
                    / (&e__ * (&q_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &p_ / (&e__ * (&q_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6482(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6482,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])/(d_.+e_.*x_),x_Symbol] :=
          Log[d+e*x]*(a+b*ArcTanh[c*x^n])/e -
          b*c*n/e \\[Star] Int[x^(n-1)*Log[d+e*x]/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && integerq!(n_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = x_.pow(&n_ - Atom::num(1)) * &linear.log()
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.log() * argument / &e__), x_)
                    - rubi_star(&b__ * &c__ * &n_ / &e__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6483(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6483,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])/(d_.+e_.*x_),x_Symbol] :=
          Log[d+e*x]*(a+b*ArcCoth[c*x^n])/e -
          b*c*n/e \\[Star] Int[x^(n-1)*Log[d+e*x]/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,n},x] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && integerq!(n_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = x_.pow(&n_ - Atom::num(1)) * &linear.log()
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.log() * argument / &e__), x_)
                    - rubi_star(&b__ * &c__ * &n_ / &e__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6484(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6484,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcTanh[c*x^(k*n)])/(d+e*x^k),x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && fractionq!(n_) },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atanh())
                / (&d__ + &e__ * sub_atom.pow(&k));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6485(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6485,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])/(d_+e_.*x_),x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcCoth[c*x^(k*n)])/(d+e*x^k),x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) && fractionq!(n_) },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acoth())
                / (&d__ + &e__ * sub_atom.pow(&k));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6486(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6486,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcTanh[c*x^n])/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[x^(n-1)*(d+e*x)^(m+1)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = x_.pow(&n_ - Atom::num(1)) * linear.pow(&m_ + Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument
                    / (&e__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6487(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6487,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCoth[c*x^n])/(e*(m+1)) -
          b*c*n/(e*(m+1)) \\[Star] Int[x^(n-1)*(d+e*x)^(m+1)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = x_.pow(&n_ - Atom::num(1)) * linear.pow(&m_ + Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument
                    / (&e__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&e__ * (&m_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6488(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6488,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcTanh[c*x^n])^p,(d+e*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,1] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 1)
                && igtq!(m_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_.pow(&n_)).atanh()).pow(&p_),
                &(&d__ + &e__ * x_).pow(&m_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6489(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6489,
        source: "Int[(d_+e_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCoth[c*x^n])^p,(d+e*x)^m,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,1] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(p_, 1)
                && igtq!(m_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_.pow(&n_)).acoth()).pow(&p_),
                &(&d__ + &e__ * x_).pow(&m_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6490(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6490,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(a+b*ArcTanh[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable((&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).atanh()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_6491(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6491,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(a+b*ArcCoth[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable((&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).acoth()).pow(&p_), x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6470_through_6491_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6470..=6491).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6470..=6491).collect::<Vec<_>>());
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
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).acoth()) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).atanh()) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_)
}
