use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5773(rules);
    push_rules_rule_5774(rules);
    push_rules_rule_5775(rules);
    push_rules_rule_5776(rules);
    push_rules_rule_5777(rules);
    push_rules_rule_5778(rules);
    push_rules_rule_5779(rules);
    push_rules_rule_5780(rules);
    push_rules_rule_5781(rules);
    push_rules_rule_5782(rules);
    push_rules_rule_5783(rules);
    push_rules_rule_5784(rules);
    push_rules_rule_5785(rules);
    push_rules_rule_5786(rules);
    push_rules_rule_5787(rules);
    push_rules_rule_5788(rules);
    push_rules_rule_5789(rules);
    push_rules_rule_5790(rules);
    push_rules_rule_5791(rules);
    push_rules_rule_5792(rules);
    push_rules_rule_5793(rules);
    push_rules_rule_5794(rules);
    push_rules_rule_5795(rules);
    push_rules_rule_5796(rules);
}

fn push_rules_rule_5773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5773,
        source: "Int[ArcSec[c_+d_.*x_],x_Symbol] :=
          (c+d*x)*ArcSec[c+d*x]/d -
          Int[1/((c+d*x)*Sqrt[1-1/(c+d*x)^2]),x] /;
        FreeQ[{c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 2.821.2, CRC 445, A&S 4.4.62", "G&R 2.821.1, CRC 446, A&S 4.4.61"],
        pattern: (c__ + d__ * x_).asec(),
        with: [c__, d__, x_],
        optional: [d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let recursive = Atom::num(1)
                / (&affine
                    * (Atom::num(1) - Atom::num(1) / affine.pow(2)).sqrt());
            rubi_simp(&(&affine * affine.asec() / &d__), x_) - rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5774,
        source: "Int[ArcCsc[c_+d_.*x_],x_Symbol] :=
          (c+d*x)*ArcCsc[c+d*x]/d +
          Int[1/((c+d*x)*Sqrt[1-1/(c+d*x)^2]),x] /;
        FreeQ[{c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 2.821.2, CRC 445, A&S 4.4.62", "G&R 2.821.1, CRC 446, A&S 4.4.61"],
        pattern: (c__ + d__ * x_).acsc(),
        with: [c__, d__, x_],
        optional: [d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let recursive = Atom::num(1)
                / (&affine
                    * (Atom::num(1) - Atom::num(1) / affine.pow(2)).sqrt());
            rubi_simp(&(&affine * affine.acsc() / &d__), x_) + rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5775,
        source: "Int[(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcSec[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.asec()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5776,
        source: "Int[(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.acsc()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5777,
        source: "Int[(a_.+b_.*ArcSec[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcSec[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * x_).asec()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5778,
        source: "Int[(a_.+b_.*ArcCsc[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCsc[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * x_).acsc()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5779,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcSec[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.asec()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5780,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.acsc()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5781,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d^(m+1) \\[Star] Subst[Int[(a+b*x)^p*Sec[x]*Tan[x]*(d*e-c*f+f*Sec[x])^m,x],x,ArcSec[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&p_)
                * sub_atom.sec()
                * sub_atom.tan()
                * (&d__ * &e__ - &c__ * &f__ + &f__ * sub_atom.sec()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ + &d__ * x_).asec(),
            );
            rubi_star(Atom::num(1) / d__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_5782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5782,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
          -1/d^(m+1) \\[Star] Subst[Int[(a+b*x)^p*Csc[x]*Cot[x]*(d*e-c*f+f*Csc[x])^m,x],x,ArcCsc[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&p_)
                * sub_atom.csc()
                * sub_atom.cot()
                * (&d__ * &e__ - &c__ * &f__ + &f__ * sub_atom.csc()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ + &d__ * x_).acsc(),
            );
            rubi_star(-Atom::num(1) / d__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_5783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5783,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSec[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = ((&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__).pow(&m_)
                * (&a__ + &b__ * sub_atom.asec()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5784,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCsc[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = ((&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__).pow(&m_)
                * (&a__ + &b__ * sub_atom.acsc()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5785,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSec[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcSec[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && !igtq!(p_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_).asec()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5786,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsc[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcCsc[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && !igtq!(p_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_).acsc()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5787,
        source: "Int[u_.*ArcSec[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcCos[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).asec().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).acos().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5788,
        source: "Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcSin[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).acsc().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).asin().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5789,
        source: "Int[u_.*f_^(c_.*ArcSec[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[ReplaceAll[u,x->-a/b+Sec[x]/b]*f^(c*x^n)*Sec[x]*Tan[x],x],x,ArcSec[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * f__.pow(c__ * (a__ + b__ * x_).asec().pow(n_)),
        with: [u__, f__, c__, a__, b__, n_, x_],
        optional: [u__, c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let replaced = rubi_replace_all(&u__, x_, -&a__ / &b__ + &sub_atom.sec() / &b__);
            let payload = replaced
                * f__.pow(&c__ * sub_atom.pow(&n_))
                * &sub_atom.sec()
                * sub_atom.tan();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).asec(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_5790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5790,
        source: "Int[u_.*f_^(c_.*ArcCsc[a_.+b_.*x_]^n_.),x_Symbol] :=
          -1/b \\[Star] Subst[Int[ReplaceAll[u,x->-a/b+Csc[x]/b]*f^(c*x^n)*Csc[x]*Cot[x],x],x,ArcCsc[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * f__.pow(c__ * (a__ + b__ * x_).acsc().pow(n_)),
        with: [u__, f__, c__, a__, b__, n_, x_],
        optional: [u__, c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let replaced = rubi_replace_all(&u__, x_, -&a__ / &b__ + &sub_atom.csc() / &b__);
            let payload = replaced
                * f__.pow(&c__ * sub_atom.pow(&n_))
                * &sub_atom.csc()
                * sub_atom.cot();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).acsc(),
            );
            rubi_star(-Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_5791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5791,
        source: "Int[ArcSec[u_],x_Symbol] :=
          x*ArcSec[u] -
          u/Sqrt[u^2] \\[Star] Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(u_).asec(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_simp(&(x_ * u_.asec()), x_)
                    - rubi_star(&u_ / u_.pow(2).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5792,
        source: "Int[ArcCsc[u_],x_Symbol] :=
          x*ArcCsc[u] +
          u/Sqrt[u^2] \\[Star] Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(u_).acsc(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_simp(&(x_ * u_.acsc()), x_)
                    + rubi_star(&u_ / u_.pow(2).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5793,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcSec[u])/(d*(m+1)) -
          b*u/(d*(m+1)*Sqrt[u^2]) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).asec()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + Atom::num(1)), &u_, x_)
                && !rubi_function_of_exponential_q(u_.as_view(), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * u_.asec();
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1)) * u_.derivative(x_) / (&u_ * radical)),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &u_
                            / (&d__ * (&m_ + Atom::num(1)) * u_.pow(2).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5794,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcCsc[u])/(d*(m+1)) +
          b*u/(d*(m+1)*Sqrt[u^2]) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).acsc()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + Atom::num(1)), &u_, x_)
                && !rubi_function_of_exponential_q(u_.as_view(), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * u_.acsc();
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1)) * u_.derivative(x_) / (&u_ * radical)),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &u_
                            / (&d__ * (&m_ + Atom::num(1)) * u_.pow(2).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 5795,
        source: "Int[v_*(a_.+b_.*ArcSec[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcSec[u]) \\[Star] w - b*u/Sqrt[u^2] \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).asec()),
        with: [v__, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_match_optional_multiplier_linear_power_q(&v__, x_)
                && rubi_int_hide_inverse_function_free_q(&v__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v__, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.asec();
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_star(argument, hidden)
                    - rubi_star(&b__ * &u_ / u_.pow(2).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 5796,
        source: "Int[v_*(a_.+b_.*ArcCsc[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcCsc[u]) \\[Star] w + b*u/Sqrt[u^2] \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[u^2-1]),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).acsc()),
        with: [v__, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_match_optional_multiplier_linear_power_q(&v__, x_)
                && rubi_int_hide_inverse_function_free_q(&v__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v__, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.acsc();
            let radical = (u_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_star(argument, hidden)
                    + rubi_star(&b__ * &u_ / u_.pow(2).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5773_through_5792_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5773..=5792).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5773..=5792).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5793_through_5796_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5793..=5796).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5793..=5796).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ + d__ * x_).acsc()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_).asec()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).acsc()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).asec()).pow(p_)
}
