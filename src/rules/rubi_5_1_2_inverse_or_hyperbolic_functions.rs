use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5136(rules);
    push_rules_rule_5137(rules);
    push_rules_rule_5138(rules);
    push_rules_rule_5139(rules);
    push_rules_rule_5140(rules);
    push_rules_rule_5141(rules);
    push_rules_rule_5142(rules);
    push_rules_rule_5143(rules);
    push_rules_rule_5144(rules);
    push_rules_rule_5145(rules);
    push_rules_rule_5146(rules);
    push_rules_rule_5147(rules);
    push_rules_rule_5148(rules);
    push_rules_rule_5149(rules);
}

fn push_rules_rule_5136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5136,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./x_,x_Symbol] :=
          Subst[Int[(a+b*x)^n*Cot[x],x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_) / x_,
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cot();
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_subst(&primitive, sub, (&c__ * x_).asin())
        },
    ));
}

fn push_rules_rule_5137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5137,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./x_,x_Symbol] :=
          -Subst[Int[(a+b*x)^n*Tan[x],x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_) / x_,
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.tan();
            let primitive = rubi_rhs_int(&payload, sub);
            -rubi_subst(&primitive, sub, (&c__ * x_).acos())
        },
    ));
}

fn push_rules_rule_5138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5138,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcSin[c*x])^n/(d*(m+1)) -
          b*c*n/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let scaled_next = (&d__ * x_).pow(&m_ + Atom::num(1));
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                &scaled_next * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(scaled_next * argument.pow(&n_) / (&d__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(-&b__ * &c__ * &n_ / (&d__ * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_5139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5139,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCos[c*x])^n/(d*(m+1)) +
          b*c*n/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let scaled_next = (&d__ * x_).pow(&m_ + Atom::num(1));
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                &scaled_next * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(scaled_next * argument.pow(&n_) / (&d__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&d__ * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_5140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5140,
        source: "Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          x^(m+1)*(a+b*ArcSin[c*x])^n/(m+1) -
          b*c*n/(m+1) \\[Star] Int[x^(m+1)*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&m_ + Atom::num(1))), x_)
                    + rubi_star(-&b__ * &c__ * &n_ / (&m_ + Atom::num(1)), recursive)
        },
    ));
}

fn push_rules_rule_5141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5141,
        source: "Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          x^(m+1)*(a+b*ArcCos[c*x])^n/(m+1) +
          b*c*n/(m+1) \\[Star] Int[x^(m+1)*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.831, CRC 453, A&S 4.4.65", "G&R 2.832, CRC 454, A&S 4.4.67"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&m_ + Atom::num(1))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&m_ + Atom::num(1)), recursive)
        },
    ));
}

fn push_rules_rule_5142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5142,
        source: "Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) -
          1/(b^2*c^(m+1)*(n+1)) \\[Star] Subst[Int[ExpandTrigReduce[x^(n+1),Sin[-a/b+x/b]^(m-1)*(m-(m+1)*Sin[-a/b+x/b]^2),x],x],x,a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]",
        desc: "Integration by parts and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(m_, 0)
                && geq!(n_, -2)
                && ltq!(n_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let trig_factor = &angle.sin().pow(&m_ - Atom::num(1))
                * (&m_ - (&m_ + Atom::num(1)) * angle.sin().pow(2));
            let expanded = rubi_expand_trig_reduce(&sub_atom.pow(&n_ + Atom::num(1)), &trig_factor, sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).asin());
            rubi_simp(&(x_.pow(&m_) * radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(-Atom::num(1)
                            / (b__.pow(2)
                                * c__.pow(&m_ + Atom::num(1))
                                * (&n_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_5143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5143,
        source: "Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) -
          1/(b^2*c^(m+1)*(n+1)) \\[Star] Subst[Int[ExpandTrigReduce[x^(n+1),Cos[-a/b+x/b]^(m-1)*(m-(m+1)*Cos[-a/b+x/b]^2),x],x],x,a+b*ArcCos[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]",
        desc: "Integration by parts and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(m_, 0)
                && geq!(n_, -2)
                && ltq!(n_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let trig_factor = &angle.cos().pow(&m_ - Atom::num(1))
                * (&m_ - (&m_ + Atom::num(1)) * angle.cos().pow(2));
            let expanded = rubi_expand_trig_reduce(&sub_atom.pow(&n_ + Atom::num(1)), &trig_factor, sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).acos());
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_) * radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(-Atom::num(1)
                            / (b__.pow(2)
                                * c__.pow(&m_ + Atom::num(1))
                                * (&n_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_5144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5144,
        source: "Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) -
          m/(b*c*(n+1)) \\[Star] Int[x^(m-1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] +
          c*(m+1)/(b*(n+1)) \\[Star] Int[x^(m+1)*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && ltq!(n_, -2) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_1_integrand =
                x_.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive_2_integrand =
                x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive_1 = rubi_rhs_int(&recursive_1_integrand, x_);
            let recursive_2 = rubi_rhs_int(&recursive_2_integrand, x_);
            rubi_simp(&(x_.pow(&m_) * radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(-&m_ / (&b__ * &c__ * (&n_ + Atom::num(1))), recursive_1)
                    + rubi_star(&c__ * (&m_ + Atom::num(1)) / (&b__ * (&n_ + Atom::num(1))), recursive_2)
        },
    ));
}

fn push_rules_rule_5145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5145,
        source: "Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -x^m*Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) +
          m/(b*c*(n+1)) \\[Star] Int[x^(m-1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] -
          c*(m+1)/(b*(n+1)) \\[Star] Int[x^(m+1)*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && ltq!(n_, -2) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_1_integrand =
                x_.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive_2_integrand =
                x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive_1 = rubi_rhs_int(&recursive_1_integrand, x_);
            let recursive_2 = rubi_rhs_int(&recursive_2_integrand, x_);
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_) * radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&m_ / (&b__ * &c__ * (&n_ + Atom::num(1))), recursive_1)
                    + rubi_star(-&c__ * (&m_ + Atom::num(1)) / (&b__ * (&n_ + Atom::num(1))), recursive_2)
        },
    ));
}

fn push_rules_rule_5146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5146,
        source: "Int[x_^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          1/(b*c^(m+1)) \\[Star] Subst[Int[x^n*Sin[-a/b+x/b]^m*Cos[-a/b+x/b],x],x,a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_) * &angle.sin().pow(&m_) * angle.cos();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).asin());
            rubi_star(Atom::num(1) / (&b__ * c__.pow(&m_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_5147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5147,
        source: "Int[x_^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -1/(b*c^(m+1)) \\[Star] Subst[Int[x^n*Cos[-a/b+x/b]^m*Sin[-a/b+x/b],x],x,a+b*ArcCos[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[m,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_) * &angle.cos().pow(&m_) * angle.sin();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).acos());
            rubi_star(-Atom::num(1) / (&b__ * c__.pow(&m_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_5148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5148,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5149,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5136_through_5142_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5136..=5142).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5136..=5142).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5143_through_5149_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5143..=5149).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5143..=5149).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}
