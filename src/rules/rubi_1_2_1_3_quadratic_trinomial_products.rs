use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    let first_rule = rules.len();
    push_rules_rule_1181(rules);
    push_rules_rule_1182(rules);
    push_rules_rule_1183(rules);
    push_rules_rule_1184(rules);
    push_rules_rule_1185(rules);
    push_rules_rule_1186(rules);
    push_rules_rule_1187(rules);
    push_rules_rule_1188(rules);
    push_rules_rule_1189(rules);
    push_rules_rule_1190(rules);
    push_rules_rule_1191(rules);
    push_rules_rule_1192(rules);
    push_rules_rule_1193(rules);
    push_rules_rule_1194(rules);
    push_rules_rule_1195(rules);
    push_rules_rule_1196(rules);
    push_rules_rule_1197(rules);
    push_rules_rule_1198(rules);
    push_rules_rule_1199(rules);
    push_rules_rule_1200(rules);
    push_rules_rule_1201(rules);
    push_rules_rule_1202(rules);
    push_rules_rule_1203(rules);
    push_rules_rule_1204(rules);
    push_rules_rule_1205(rules);
    push_rules_rule_1206(rules);
    push_rules_rule_1207(rules);
    push_rules_rule_1208(rules);
    push_rules_rule_1209(rules);
    push_rules_rule_1210(rules);
    push_rules_rule_1211(rules);
    push_rules_rule_1212(rules);
    push_rules_rule_1213(rules);
    push_rules_rule_1214(rules);
    push_rules_rule_1215(rules);
    push_rules_rule_1216(rules);
    push_rules_rule_1217(rules);
    push_rules_rule_1218(rules);
    push_rules_rule_1219(rules);
    push_rules_rule_1220(rules);
    push_rules_rule_1221(rules);
    push_rules_rule_1222(rules);
    push_rules_rule_1223(rules);
    push_rules_rule_1224(rules);
    push_rules_rule_1225(rules);
    push_rules_rule_1226(rules);
    push_rules_rule_1227(rules);
    push_rules_rule_1228(rules);
    push_rules_rule_1229(rules);
    push_rules_rule_1230(rules);
    push_rules_rule_1231(rules);
    push_rules_rule_1232(rules);
    push_rules_rule_1233(rules);
    push_rules_rule_1234(rules);
    push_rules_rule_1235(rules);
    push_rules_rule_1236(rules);
    push_rules_rule_1237(rules);
    push_rules_rule_1238(rules);
    push_rules_rule_1239(rules);
    push_rules_rule_1240(rules);
    push_rules_rule_1241(rules);
    push_rules_rule_1242(rules);
    push_rules_rule_1243(rules);
    push_rules_rule_1244(rules);
    push_rules_rule_1245(rules);
    push_rules_rule_1246(rules);
    push_rules_rule_1247(rules);
    push_rules_rule_1248(rules);
    push_rules_rule_1249(rules);
    push_rules_rule_1250(rules);
    push_rules_rule_1251(rules);
    push_rules_rule_1252(rules);
    push_rules_rule_1253(rules);
    push_rules_rule_1254(rules);
    push_rules_rule_1255(rules);
    push_rules_rule_1256(rules);
    push_rules_rule_1257(rules);
    push_rules_rule_1258(rules);
    push_rules_rule_1259(rules);
    push_rules_rule_1260(rules);
    push_rules_rule_1261(rules);
    push_rules_rule_1262(rules);
    push_rules_rule_1263(rules);
    push_rules_rule_1264(rules);
    push_rules_rule_1265(rules);
    push_rules_rule_1266(rules);
    push_rules_rule_1267(rules);
    push_rules_rule_1268(rules);
    push_rules_rule_1269(rules);
    push_rules_rule_1270(rules);
    push_rules_rule_1271(rules);
    push_rules_rule_1272(rules);
    push_rules_rule_1273(rules);
    push_rules_rule_1274(rules);
    push_rules_rule_1275(rules);
    push_rules_rule_1276(rules);
    push_rules_rule_1277(rules);
    push_rules_rule_1278(rules);
    push_rules_rule_1279(rules);
    push_rules_rule_1280(rules);
    push_rules_rule_1281(rules);
    push_rules_rule_1282(rules);
    push_rules_rule_1283(rules);
    push_rules_rule_1284(rules);
    push_rules_rule_1285(rules);
    push_rules_rule_1286(rules);
    push_rules_rule_1287(rules);
    push_rules_rule_1288(rules);
    push_rules_rule_1289(rules);
    push_rules_rule_1290(rules);
    push_rules_rule_1291(rules);
    push_rules_rule_1292(rules);
    push_rules_rule_1293(rules);
    for rule in &mut rules[first_rule..] {
        match rule.downvalue_order {
            Some(1181..=1183) => rule.require_proportional_affine_factor_pair = true,
            Some(1184..=1187) => rule.require_perfect_square_quadratic_base = true,
            Some(1188..=1191) => rule.require_opposite_binomial_base_pair = true,
            Some(1192) => rule.require_half_integer_affine_power = true,
            Some(1193) => rule.require_negative_scaled_affine_and_distinct_noninteger_affine = true,
            Some(1194) => rule.required_noninteger_affine_power_count = 2,
            _ => {}
        }
    }
}

fn push_rules_rule_1181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1181,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (g/e)^n \\[Star] Int[(d+e*x)^(m+n)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[e*f-d*g,0] && IntegerQ[n] && Not[IntegerQ[m] && SimplerQ[f+g*x,d+e*x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && integerq!(n_)
                && !(integerq!(m_)
                    && simplerq!(&f__ + &g__ * x_, &d__ + &e__ * x_))
        },
        rhs: {
            let recursive_integrand = (&d__ + &e__ * x_).pow(&m_ + &n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star((&g__ / &e__).pow(&n_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1182,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (e/g)^m \\[Star] Int[(f+g*x)^(m+n)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[e*f-d*g,0] && GtQ[e/g,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && gtq!(&e__ / &g__, 0)
        },
        rhs: {
            let recursive_integrand = (&f__ + &g__ * x_).pow(&m_ + &n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star((&e__ / &g__).pow(&m_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1183,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^m/(f+g*x)^m \\[Star] Int[(f+g*x)^(m+n)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[e*f-d*g,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
        },
        rhs: {
            let first_linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let recursive_integrand = second_linear.pow(&m_ + &n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star(first_linear.pow(&m_) / second_linear.pow(&m_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1184,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          1/c^p \\[Star] Int[(d+e*x)^m*(f+g*x)^n*(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1188,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[(d*f+e*g*x^2)^m*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[m,n] && EqQ[e*f+d*g,0] && (IntegerQ[m] || GtQ[d,0] && GtQ[f,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, g__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(m_, n_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && (integerq!(m_) || gtq!(d__, 0) && gtq!(f__, 0))
        },
        rhs: {
            let recursive_integrand = (&d__ * &f__ + &e__ * &g__ * x_.pow(2)).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1189,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          b \\[Star] Int[x*(d+e*x)^m*(f+g*x)^n,x] + Int[(d+e*x)^m*(f+g*x)^n*(a+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && EqQ[m,n] && EqQ[e*f+d*g,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(n_)
            * (a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, e__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && eqq!(m_, n_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
        },
        rhs: {
            let linear_product = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_);
            let first_integrand = x_ * &linear_product;
            let second_integrand = linear_product * (&a__ + &c__ * x_.pow(2));
            rubi_star(b__, rubi_rhs_int(&first_integrand, x_))
                    + rubi_rhs_int(&second_integrand, x_)
        },
    ));
}

fn push_rules_rule_1190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1190,
        source: "Int[Sqrt[d_+e_.*x_]*Sqrt[f_+g_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*g/c \\[Star] Int[1/(Sqrt[d+e*x]*Sqrt[f+g*x]),x] +
          1/c \\[Star] Int[(c*d*f-a*e*g-b*e*g*x)/(Sqrt[d+e*x]*Sqrt[f+g*x]*(a+b*x+c*x^2)),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e*f+d*g,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt() * (f__ + g__ * x_).sqrt()
            / (a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, e__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
        },
        rhs: {
            let radical_product = (&d__ + &e__ * x_).sqrt()
                * (&f__ + &g__ * x_).sqrt();
            let first_integrand = Atom::num(1) / &radical_product;
            let second_integrand = (&c__ * &d__ * &f__
                - &a__ * &e__ * &g__
                - &b__ * &e__ * &g__ * x_)
                / (radical_product * (&a__ + &b__ * x_ + &c__ * x_.pow(2)));
            rubi_star(&e__ * &g__ / &c__, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1191,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^FracPart[m]*(f+g*x)^FracPart[m]/(d*f+e*g*x^2)^FracPart[m] \\[Star] Int[(d*f+e*g*x^2)^m*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[m,n] && EqQ[e*f+d*g,0] && Not[EqQ[p,2] && LtQ[m,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(m_, n_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && !(eqq!(p_, 2) && ltq!(m_, -1))
        },
        rhs: {
            let first_linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let merged_quadratic = &d__ * &f__ + &e__ * &g__ * x_.pow(2);
            let fractional_part = rubi_frac_part(&m_);
            let prefactor = first_linear.pow(&fractional_part)
                * second_linear.pow(&fractional_part)
                / merged_quadratic.pow(&fractional_part);
            let recursive_integrand = merged_quadratic.pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            rubi_star(prefactor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1193,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x+c*x^2)^p,d+e*x,x],R=PolynomialRemainder[(a+b*x+c*x^2)^p,d+e*x,x]},
          R*(d+e*x)^(m+1)*(f+g*x)^(n+1)/((m+1)*(e*f-d*g)) +
          1/((m+1)*(e*f-d*g)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^n*ExpandToSum[(m+1)*(e*f-d*g)*Qx-g*R*(m+n+2),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && IGtQ[p,0] && ILtQ[2*m,-2] && Not[IntegerQ[n]] && Not[EqQ[m,-2] && EqQ[p,1] && EqQ[2*c*d-b*e,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && igtq!(p_, 0)
                && iltq!(Atom::num(2) * &m_, -2)
                && !integerq!(n_)
                && !(eqq!(m_, -2)
                    && eqq!(p_, 1)
                    && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let (quotient, remainder) =
                polynomial_quotient_remainder(&quadratic.pow(&p_), &linear, x_).rubi_rhs();
            let m_plus_one = &m_ + Atom::num(1);
            let denominator = &m_plus_one * (&e__ * &f__ - &d__ * &g__);
            let payload = rubi_expand_to_sum(
                &(&m_plus_one * (&e__ * &f__ - &d__ * &g__) * quotient
                    - &g__ * &remainder * (&m_ + &n_ + Atom::num(2))),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_one) * second_linear.pow(&n_) * payload;
            rubi_simp(&(remainder
                    * linear.pow(&m_plus_one)
                    * second_linear.pow(&n_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1194,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          c^p*(d+e*x)^(m+2*p)*(f+g*x)^(n+1)/(g*e^(2*p)*(m+n+2*p+1)) +
          1/(g*e^(2*p)*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(f+g*x)^n*
            ExpandToSum[g*(m+n+2*p+1)*(e^(2*p)*(a+b*x+c*x^2)^p-c^p*(d+e*x)^(2*p))-c^p*(e*f-d*g)*(m+2*p)*(d+e*x)^(2*p-1),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && NeQ[m+n+2*p+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(p_, 0)
                && !integerq!(m_)
                && !integerq!(n_)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let c_p = c__.pow(&p_);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let exponent_sum = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let denominator = &g__ * &e_2p * &exponent_sum;
            let payload = rubi_expand_to_sum(
                &(&g__
                    * &exponent_sum
                    * (&e_2p * quadratic.pow(&p_)
                        - &c_p * linear.pow(Atom::num(2) * &p_))
                    - &c_p
                        * (&e__ * &f__ - &d__ * &g__)
                        * (&m_ + Atom::num(2) * &p_)
                        * linear.pow(Atom::num(2) * &p_ - Atom::num(1))),
                x_,
            );
            let recursive_integrand =
                linear.pow(&m_) * second_linear.pow(&n_) * payload;
            rubi_simp(&(c_p
                    * linear.pow(&m_ + Atom::num(2) * &p_)
                    * second_linear.pow(&n_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1195,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1199,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          With[{q=Denominator[m]},
          q/e \\[Star] Subst[Int[ExpandIntegrand[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n/((c*d^2-b*d*e+a*e^2)/e^2-(2*c*d-b*e)*x^q/e^2+c*x^(2*q)/e^2),x],x],x,(d+e*x)^(1/q)]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[n] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(n_)
                && fractionq!(m_)
        },
        rhs: {
            let q = Atom::num(rational_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let sub_q = sub_atom.pow(&q);
            let transformed_integrand = sub_atom.pow(&q * (&m_ + Atom::num(1)) - Atom::num(1))
                * ((&e__ * &f__ - &d__ * &g__) / &e__ + &g__ * &sub_q / &e__).pow(&n_)
                / ((&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2))
                    / e__.pow(2)
                    - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * &sub_q
                        / e__.pow(2)
                    + &c__ * sub_atom.pow(Atom::num(2) * &q) / e__.pow(2));
            let expanded = rubi_expand_integrand(&transformed_integrand, sub_symbol);
            let transformed = rubi_rhs_int(&expanded, sub_symbol);
            let substitution = (&d__ + &e__ * x_).pow(Atom::num(1) / &q);
            rubi_star(&q / &e__, rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1200,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_./(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n/(a+b*x+c*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && IntegersQ[n]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && integersq!([n_])
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1201,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          g/c^2 \\[Star] Int[Simp[2*c*e*f+c*d*g-b*e*g+c*e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] +
          1/c^2 \\[Star] Int[Simp[c^2*d*f^2-2*a*c*e*f*g-a*c*d*g^2+a*b*e*g^2+(c^2*e*f^2+2*c^2*d*f*g-2*b*c*e*f*g-b*c*d*g^2+b^2*e*g^2-a*c*e*g^2)*x,x]*
            (d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_payload = simp!(
                Atom::num(2) * &c__ * &e__ * &f__ + &c__ * &d__ * &g__
                    - &b__ * &e__ * &g__
                    + &c__ * &e__ * &g__ * x_,
                x_
            );
            let first_integrand = first_payload
                * linear.pow(&m_ - Atom::num(1))
                * second_linear.pow(&n_ - Atom::num(2));
            let second_payload = simp!(
                c__.pow(2) * &d__ * f__.pow(2)
                    - Atom::num(2) * &a__ * &c__ * &e__ * &f__ * &g__
                    - &a__ * &c__ * &d__ * g__.pow(2)
                    + &a__ * &b__ * &e__ * g__.pow(2)
                    + (c__.pow(2) * &e__ * f__.pow(2)
                        + Atom::num(2) * c__.pow(2) * &d__ * &f__ * &g__
                        - Atom::num(2) * &b__ * &c__ * &e__ * &f__ * &g__
                        - &b__ * &c__ * &d__ * g__.pow(2)
                        + b__.pow(2) * &e__ * g__.pow(2)
                        - &a__ * &c__ * &e__ * g__.pow(2))
                        * x_,
                x_
            );
            let second_integrand = second_payload
                * linear.pow(&m_ - Atom::num(1))
                * second_linear.pow(&n_ - Atom::num(2))
                / quadratic;
            rubi_star(&g__ / c__.pow(2), rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / c__.pow(2), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1202,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*g/c \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] +
          1/c \\[Star] Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g-b*e*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] &&
          Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_integrand =
                linear.pow(&m_ - Atom::num(1)) * second_linear.pow(&n_ - Atom::num(1));
            let payload = simp!(
                &c__ * &d__ * &f__ - &a__ * &e__ * &g__
                    + (&c__ * &e__ * &f__ + &c__ * &d__ * &g__
                        - &b__ * &e__ * &g__)
                        * x_,
                x_
            );
            let second_integrand = payload
                * linear.pow(&m_ - Atom::num(1))
                * second_linear.pow(&n_ - Atom::num(1))
                / quadratic;
            rubi_star(&e__ * &g__ / &c__, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1203,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          -g*(e*f-d*g)/(c*f^2-b*f*g+a*g^2) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n,x] +
          1/(c*f^2-b*f*g+a*g^2) \\[Star]
            Int[Simp[c*d*f-b*d*g+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] &&
          Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && LtQ[n,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && gtq!(m_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &c__ * f__.pow(2) - &b__ * &f__ * &g__ + &a__ * g__.pow(2);
            let first_integrand =
                linear.pow(&m_ - Atom::num(1)) * second_linear.pow(&n_);
            let payload = simp!(
                &c__ * &d__ * &f__ - &b__ * &d__ * &g__ + &a__ * &e__ * &g__
                    + &c__ * (&e__ * &f__ - &d__ * &g__) * x_,
                x_
            );
            let second_integrand = payload
                * linear.pow(&m_ - Atom::num(1))
                * second_linear.pow(&n_ + Atom::num(1))
                / quadratic;
            rubi_star(-&g__ * (&e__ * &f__ - &d__ * &g__) / &denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1204,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
          Int[ExpandIntegrand[1/(Sqrt[d+e*x]*Sqrt[f+g*x]),(d+e*x)^(m+1/2)/(a+b*x+c*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m+1/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            / ((f__ + g__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let first_factor = Atom::num(1)
                / ((&d__ + &e__ * x_).sqrt()
                    * (&f__ + &g__ * x_).sqrt());
            let second_factor = (&d__ + &e__ * x_)
                .pow(&m_ + Atom::num(1) / Atom::num(2))
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded =
                rubi_expand_integrand_product(&first_factor, &second_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1205,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+b*x+c*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let first_factor = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_);
            let second_factor =
                Atom::num(1) / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded =
                rubi_expand_integrand_product(&first_factor, &second_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1206,
        source: "Int[(d_+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^p*(d+e*x)^m*(f+g*x)^n*(b+c*x)^p,x],x] /;
        FreeQ[{b,c,d,e,f,g},x] && ILtQ[p,-1] && IntegersQ[m,n]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(n_)
            * (b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, e__, g__, m_, n_],
        when: {
            freeq!([b__, c__, d__, e__, f__, g__], x_)
                && iltq!(p_, -1)
                && integersq!([m_, n_])
        },
        rhs: {
            let integrand = x_.pow(&p_)
                * (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&b__ + &c__ * x_).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1207,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
            1/c^p \\[Star] Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(b/2-q/2+c*x)^p*(b/2+q/2+c*x)^p,x],x] /;
         Not[FractionalPowerFactorQ[q]]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[p,-1] && IntegersQ[m,n] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && iltq!(p_, -1)
                && integersq!([m_, n_])
                && rubi_nice_sqrt_q(&discriminant)
                && !rubi_fractional_power_factor_q(&q)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_).pow(&p_)
                * (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_1208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1208,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          g^2*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b*e*g*(m+p+2)+2*c*(d*g*(p+1)-e*f*(m+2*p+3)),0] &&
          EqQ[e*(c*f^2-b*f*g+a*g^2)*(m+1)+(2*c*f-b*g)*(e*f-d*g)*(p+1),0] && NeQ[m+2*p+3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(2)
            * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(
                    &b__ * &e__ * &g__ * (&m_ + &p_ + Atom::num(2))
                        + Atom::num(2)
                            * &c__
                            * (&d__ * &g__ * (&p_ + Atom::num(1))
                                - &e__
                                    * &f__
                                    * (&m_ + Atom::num(2) * &p_ + Atom::num(3))),
                    0
                )
                && eqq!(
                    &e__
                        * (&c__ * f__.pow(2) - &b__ * &f__ * &g__
                            + &a__ * g__.pow(2))
                        * (&m_ + Atom::num(1))
                        + (Atom::num(2) * &c__ * &f__ - &b__ * &g__)
                            * (&e__ * &f__ - &d__ * &g__)
                            * (&p_ + Atom::num(1)),
                    0
                )
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
        },
        rhs: {
            rubi_simp(&(g__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / (&c__
                        * &e__
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))), x_)
        },
    ));
}

fn push_rules_rule_1209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1209,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(f+g*x)^n*(a*d+c*e*x^3)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0] && EqQ[m,p] && ILtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&b__ * &d__ + &a__ * &e__, 0)
                && eqq!(&c__ * &d__ + &b__ * &e__, 0)
                && eqq!(m_, p_)
                && iltq!(p_, -1)
        },
        rhs: {
            let integrand = (&f__ + &g__ * x_).pow(&n_)
                * (&a__ * &d__ + &c__ * &e__ * x_.pow(3)).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1210,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^FracPart[p]*(a+b*x+c*x^2)^FracPart[p]/(a*d+c*e*x^3)^FracPart[p] \\[Star] Int[(f+g*x)^n*(a*d+c*e*x^3)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0] && EqQ[m,p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&b__ * &d__ + &a__ * &e__, 0)
                && eqq!(&c__ * &d__ + &b__ * &e__, 0)
                && eqq!(m_, p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let collapsed = &a__ * &d__ + &c__ * &e__ * x_.pow(3);
            let integrand = (&f__ + &g__ * x_).pow(&n_) * collapsed.pow(&p_);
            rubi_star(linear.pow(&frac_p) * quadratic.pow(&frac_p)
                    / collapsed.pow(&frac_p), rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_1211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1211,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_./(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2*(2*c*d-b*e)^(m-2)*(c*(e*f+d*g)-b*e*g)^n*(d+e*x)/(c^(m+n-1)*e^(n-1)*Sqrt[a+b*x+c*x^2]) +
          1/(c^(m+n-1)*e^(n-2)) \\[Star]
            Int[ExpandToSum[((2*c*d-b*e)^(m-1)*(c*(e*f+d*g)-b*e*g)^n-c^(m+n-1)*e^n*(d+e*x)^(m-1)*(f+g*x)^n)/(c*d-b*e-c*e*x),x]/Sqrt[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_)
            / (a__ + b__ * x_ + c__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let alpha = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let beta = &c__ * (&e__ * &f__ + &d__ * &g__) - &b__ * &e__ * &g__;
            let exponent_sum = &m_ + &n_ - Atom::num(1);
            let direct = -Atom::num(2)
                * alpha.pow(&m_ - Atom::num(2))
                * beta.pow(&n_)
                * &linear
                / (c__.pow(&exponent_sum)
                    * e__.pow(&n_ - Atom::num(1))
                    * quadratic.sqrt());
            let numerator = alpha.pow(&m_ - Atom::num(1)) * beta.pow(&n_)
                - c__.pow(&exponent_sum)
                    * e__.pow(&n_)
                    * linear.pow(&m_ - Atom::num(1))
                    * second_linear.pow(&n_);
            let expanded = rubi_expand_to_sum(
                &(numerator
                    / (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)),
                x_,
            );
            let recursive_integrand = expanded / quadratic.sqrt();
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1)
                            / (c__.pow(&exponent_sum)
                                * e__.pow(&n_ - Atom::num(2))), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1212,
        source: "Int[x_^n_.*(d_.+e_.*x_)^m_./(a_+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2*(2*c*d-b*e)^(m-2)*(c*d-b*e)^n*(d+e*x)/(c^(m+n-1)*e^(n-1)*Sqrt[a+b*x+c*x^2]) -
          e^2/c^(m+n-1) \\[Star]
            Int[ExpandToSum[(c^(m+n-1)*(d+e*x)^(m-1)-((c*d-b*e)^n*(2*c*d-b*e)^(m-1))*e^(-n)*x^(-n))/(c*d-b*e-c*e*x),x]/(Sqrt[a+b*x+c*x^2]/x^n),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[m,0] && ILtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(n_) * (d__ + e__ * x_).pow(m_)
            / (a__ + b__ * x_ + c__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let alpha = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let beta = &c__ * &d__ - &b__ * &e__;
            let exponent_sum = &m_ + &n_ - Atom::num(1);
            let direct = -Atom::num(2)
                * alpha.pow(&m_ - Atom::num(2))
                * beta.pow(&n_)
                * &linear
                / (c__.pow(&exponent_sum)
                    * e__.pow(&n_ - Atom::num(1))
                    * quadratic.sqrt());
            let numerator = c__.pow(&exponent_sum) * linear.pow(&m_ - Atom::num(1))
                - beta.pow(&n_)
                    * alpha.pow(&m_ - Atom::num(1))
                    * e__.pow(-&n_)
                    * x_.pow(-&n_);
            let expanded = rubi_expand_to_sum(
                &(numerator / (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)),
                x_,
            );
            let recursive_integrand =
                expanded / (quadratic.sqrt() / x_.pow(&n_));
            rubi_simp(&(direct), x_)
                    - rubi_star(e__.pow(2) / c__.pow(&exponent_sum), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1213,
        source: "Int[x_^n_.*(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -2*(-d)^n*e^(2*m-n+3)*Sqrt[a+b*x+c*x^2]/((-2*c*d+b*e)^(m+2)*(d+e*x)) -
          e^(2*m-n+2) \\[Star] Int[ExpandToSum[((-d)^n*(-2*c*d+b*e)^(-m-1)-e^n*x^n*((-c)*d+b*e+c*e*x)^(-m-1))/(d+e*x),x]/Sqrt[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[m,0] && IGtQ[n,0] && EqQ[m+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && igtq!(n_, 0)
                && eqq!(&m_ + &p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let alpha = -Atom::num(2) * &c__ * &d__ + &b__ * &e__;
            let affine = -&c__ * &d__ + &b__ * &e__ + &c__ * &e__ * x_;
            let direct = -Atom::num(2)
                * (-&d__).pow(&n_)
                * e__.pow(Atom::num(2) * &m_ - &n_ + Atom::num(3))
                * quadratic.sqrt()
                / (alpha.pow(&m_ + Atom::num(2)) * &linear);
            let numerator = (-&d__).pow(&n_)
                * alpha.pow(-&m_ - Atom::num(1))
                - e__.pow(&n_)
                    * x_.pow(&n_)
                    * affine.pow(-&m_ - Atom::num(1));
            let expanded = rubi_expand_to_sum(&(numerator / &linear), x_);
            let recursive_integrand = expanded / quadratic.sqrt();
            rubi_simp(&(direct), x_)
                    - rubi_star(e__.pow(Atom::num(2) * &m_ - &n_ + Atom::num(2)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1214,
        source: "Int[x_^n_.*(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -2*(-d)^n*e^(2*m-n+3)*Sqrt[a+b*x+c*x^2]/((-2*c*d+b*e)^(m+2)*(d+e*x)) -
          e^(2*m+2) \\[Star] Int[ExpandToSum[((-d)^n*(-2*c*d+b*e)^(-m-1)*e^(-n)*x^(-n)-(-c*d+b*e+c*e*x)^(-m-1))/(d+e*x),x]/(x^(-n)*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[m,0] && ILtQ[n,0] && EqQ[m+p,-3/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && iltq!(n_, 0)
                && eqq!(&m_ + &p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let alpha = -Atom::num(2) * &c__ * &d__ + &b__ * &e__;
            let affine = -&c__ * &d__ + &b__ * &e__ + &c__ * &e__ * x_;
            let direct = -Atom::num(2)
                * (-&d__).pow(&n_)
                * e__.pow(Atom::num(2) * &m_ - &n_ + Atom::num(3))
                * quadratic.sqrt()
                / (alpha.pow(&m_ + Atom::num(2)) * &linear);
            let numerator = (-&d__).pow(&n_)
                * alpha.pow(-&m_ - Atom::num(1))
                * e__.pow(-&n_)
                * x_.pow(-&n_)
                - affine.pow(-&m_ - Atom::num(1));
            let expanded = rubi_expand_to_sum(&(numerator / &linear), x_);
            let recursive_integrand =
                expanded / (x_.pow(-&n_) * quadratic.sqrt());
            rubi_simp(&(direct), x_)
                    - rubi_star(e__.pow(Atom::num(2) * &m_ + Atom::num(2)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1215,
        source: "Int[(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          Int[(a/d+c*x/e)*(f+g*x)^n*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let integrand = (&a__ / &d__ + &c__ * x_ / &e__)
                * (&f__ + &g__ * x_).pow(&n_)
                * quadratic.pow(&p_ - Atom::num(1));
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1216,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Int[(a/d+c*x/e)^(-m)*(f+g*x)^n*(a+b*x+c*x^2)^(m+1/2),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[m,0] && IntegerQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(n_)
            * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, x_],
        optional: [a__, b__, c__, e__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && integerq!(n_)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let integrand = (&a__ / &d__ + &c__ * x_ / &e__).pow(-&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * quadratic.pow(&m_ + Atom::num(1) / Atom::num(2));
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1185,
        source: "Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -f*g*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(e*f-d*g)) /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b^2-4*a*c,0] && EqQ[m+2*p+3,0] && EqQ[2*c*f-b*g,0]",
        desc: "Quadratic recurrence 2a with 2 c f-b g\\[Equal]0 : square quadratic recurrence 3b with m+2 p+3\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [b__, c__, d__, e__, g__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && eqq!(Atom::num(2) * &c__ * &f__ - &b__ * &g__, 0)
        },
        rhs: {
            let denominator = &b__ * (&p_ + Atom::num(1)) * (&e__ * &f__ - &d__ * &g__);
            rubi_simp(&(-&f__ * &g__ * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1222,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) -
          e*g*m/(2*c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[2*c*f-b*g,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(Atom::num(2) * &c__ * &f__ - &b__ * &g__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * (&p_ + Atom::num(1));
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &g__ * linear.pow(&m_) * quadratic.pow(&p_ + Atom::num(1)) / &denominator;
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1));
            rubi_simp(&(direct), x_)
                    - rubi_star(&e__ * &g__ * &m_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1192,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          2/e^(n+2*p+1) \\[Star] Subst[Int[x^(2*m+1)*(e*f-d*g+g*x^2)^n*(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4)^p,x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[p,0] && ILtQ[n,0] && IntegerQ[m+1/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && integerq!(&m_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_quartic = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2)
                - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * sub_atom.pow(2)
                + &c__ * sub_atom.pow(4);
            let transformed_integrand = sub_atom.pow(Atom::num(2) * &m_ + Atom::num(1))
                * (&e__ * &f__ - &d__ * &g__ + &g__ * sub_atom.pow(2)).pow(&n_)
                * transformed_quartic.pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            let substitution = (&d__ + &e__ * x_).sqrt();

            rubi_star(Atom::num(2) / e__.pow(&n_ + Atom::num(2) * &p_ + Atom::num(1)), rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1186,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -2*c*(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)^2) +
          (2*c*f-b*g)/(2*c*d-b*e) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b^2-4*a*c,0] && EqQ[m+2*p+3,0] && NeQ[2*c*f-b*g,0] && NeQ[2*c*d-b*e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && neq!(Atom::num(2) * &c__ * &f__ - &b__ * &g__, 0)
                && neq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let linear_coefficient = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct_denominator = (&p_ + Atom::num(1)) * linear_coefficient.pow(2);
            let linear = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = -Atom::num(2)
                * &c__
                * (&e__ * &f__ - &d__ * &g__)
                * linear.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / direct_denominator;
            let recursive_integrand = linear.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_);
            rubi_simp(&(direct), x_) + rubi_star((Atom::num(2) * &c__ * &f__ - &b__ * &g__) / linear_coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1187,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p])) \\[Star] Int[(d+e*x)^m*(f+g*x)^n*(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ / Atom::num(2) + &c__ * x_;
            let frac_part = rubi_frac_part(&p_);
            let int_part = rubi_int_part(&p_);
            let recursive_integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * linear.pow(Atom::num(2) * &p_);
            let prefactor = trinomial.pow(&frac_part)
                / (c__.pow(&int_part) * linear.pow(Atom::num(2) * frac_part));
            rubi_star(prefactor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 1223,
        source: "Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3),0] && NeQ[p,-1]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            let two_p_plus_three = Atom::num(2) * &p_ + Atom::num(3);
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(
                    b__.pow(2) * &e__ * &g__ * (&p_ + Atom::num(2))
                        - Atom::num(2) * &a__ * &c__ * &e__ * &g__
                        + &c__ * (Atom::num(2) * &c__ * &d__ * &f__ - &b__ * (&e__ * &f__ + &d__ * &g__)) * two_p_plus_three,
                    0
                )
                && neq!(p_, -1)
        },
        rhs: {
            let two_p_plus_three = Atom::num(2) * &p_ + Atom::num(3);
            let p_plus_one = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * c__.pow(2) * &p_plus_one * &two_p_plus_three;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let numerator = &b__ * &e__ * &g__ * (&p_ + Atom::num(2))
                - &c__ * (&e__ * &f__ + &d__ * &g__) * &two_p_plus_three
                - Atom::num(2) * &c__ * &e__ * &g__ * &p_plus_one * x_;

            rubi_simp(&(-numerator * trinomial.pow(p_plus_one) / denominator), x_)
        },
    ));
}

fn push_rules_rule_1224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 1224,
        source: "Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(b^2*e*g-b*c*(e*f+d*g)+2*c*(c*d*f-a*e*g))*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(b^2-4*a*c)) -
          (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(c*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && LtQ[p,-1] && Not[IntegerQ[p] && NeQ[a,0] && NiceSqrtQ[b^2-4*a*c]]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && !(integerq!(p_) && neq!(a__, 0) && rubi_nice_sqrt_q(&discriminant))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p_plus_one = &p_ + Atom::num(1);
            let denominator = &c__ * &p_plus_one * &discriminant;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_numerator = Atom::num(2) * &a__ * &c__ * (&e__ * &f__ + &d__ * &g__)
                - &b__ * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__)
                - (b__.pow(2) * &e__ * &g__
                    - &b__ * &c__ * (&e__ * &f__ + &d__ * &g__)
                    + Atom::num(2) * &c__ * (&c__ * &d__ * &f__ - &a__ * &e__ * &g__))
                    * x_;
            let recursive_coefficient = b__.pow(2) * &e__ * &g__ * (&p_ + Atom::num(2))
                - Atom::num(2) * &a__ * &c__ * &e__ * &g__
                + &c__
                    * (Atom::num(2) * &c__ * &d__ * &f__ - &b__ * (&e__ * &f__ + &d__ * &g__))
                    * (Atom::num(2) * &p_ + Atom::num(3));
            let recursive_integrand = trinomial.pow(&p_ + Atom::num(1));
            rubi_simp(&(-direct_numerator * trinomial.pow(p_plus_one) / &denominator), x_)
                    - rubi_star(recursive_coefficient / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 1225,
        source: "Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) +
          (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(2*c^2*(2*p+3)) \\[Star] Int[(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && Not[LeQ[p,-1]]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && !leq!(p_, -1)
        },
        rhs: {
            let two_p_plus_three = Atom::num(2) * &p_ + Atom::num(3);
            let p_plus_one = &p_ + Atom::num(1);
            let direct_denominator = Atom::num(2) * c__.pow(2) * &p_plus_one * &two_p_plus_three;
            let recursive_denominator = Atom::num(2) * c__.pow(2) * &two_p_plus_three;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_numerator = &b__ * &e__ * &g__ * (&p_ + Atom::num(2))
                - &c__ * (&e__ * &f__ + &d__ * &g__) * &two_p_plus_three
                - Atom::num(2) * &c__ * &e__ * &g__ * &p_plus_one * x_;
            let recursive_coefficient = b__.pow(2) * &e__ * &g__ * (&p_ + Atom::num(2))
                - Atom::num(2) * &a__ * &c__ * &e__ * &g__
                + &c__
                    * (Atom::num(2) * &c__ * &d__ * &f__ - &b__ * (&e__ * &f__ + &d__ * &g__))
                    * &two_p_plus_three;
            let recursive_integrand = trinomial.pow(&p_);
            rubi_simp(&(-direct_numerator * trinomial.pow(p_plus_one) / direct_denominator), x_)
                    + rubi_star(recursive_coefficient / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1217,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[c*e*f*(m+2*p+2)+g*(c*d*m-b*e*(m+p+1)),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(
                    &m_ * (&g__ * (&c__ * &d__ - &b__ * &e__) + &c__ * &e__ * &f__)
                        + &e__ * (&p_ + Atom::num(1)) * (Atom::num(2) * &c__ * &f__ - &b__ * &g__),
                    0
                )
        },
        rhs: {
            let denominator = &c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2));
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);

            rubi_simp(&(&g__ * linear.pow(&m_) * trinomial.pow(&p_ + Atom::num(1)) / denominator), x_)
        },
    ));
}

fn push_rules_rule_1218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1218,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) -
          e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e)) \\[Star]
            Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let p_plus_one = &p_ + Atom::num(1);
            let shared = &g__ * (&c__ * &d__ - &b__ * &e__) + &c__ * &e__ * &f__;
            let denominator = &c__ * &p_plus_one * (Atom::num(2) * &c__ * &d__ - &b__ * &e__);
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_coefficient =
                &e__ * (&m_ * &shared + &e__ * &p_plus_one * (Atom::num(2) * &c__ * &f__ - &b__ * &g__));
            let recursive_integrand = linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_plus_one);
            rubi_simp(&(shared * linear.pow(&m_) * trinomial.pow(&p_plus_one) / &denominator), x_)
                    - rubi_star(recursive_coefficient / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1219,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) -
          e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e)) \\[Star]
            Int[(d+e*x)^Simplify[m-1]*(a+b*x+c*x^2)^Simplify[p+1],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && sum_simplerq!(p_, 1)
                && sum_simplerq!(m_, -1)
                && neq!(p_, -1)
        },
        rhs: {
            let p_plus_one = rubi_simplify(&(&p_ + Atom::num(1)));
            let m_minus_one = rubi_simplify(&(&m_ - Atom::num(1)));
            let shared = &g__ * (&c__ * &d__ - &b__ * &e__) + &c__ * &e__ * &f__;
            let denominator = &c__ * (&p_ + Atom::num(1)) * (Atom::num(2) * &c__ * &d__ - &b__ * &e__);
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_coefficient =
                &e__ * (&m_ * &shared + &e__ * (&p_ + Atom::num(1)) * (Atom::num(2) * &c__ * &f__ - &b__ * &g__));
            let recursive_integrand = linear.pow(m_minus_one) * trinomial.pow(&p_plus_one);
            rubi_simp(&(shared * linear.pow(&m_) * trinomial.pow(&p_plus_one) / &denominator), x_)
                    - rubi_star(recursive_coefficient / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1220,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d*g-e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((2*c*d-b*e)*(m+p+1)) +
          (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(e*(2*c*d-b*e)*(m+p+1)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] &&
          (LtQ[m,-1] && Not[IGtQ[m+p+1,0]] || LtQ[m,0] && LtQ[p,-1] || EqQ[m+2*p+2,0]) && NeQ[m+p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            let m_p_1 = &m_ + &p_ + Atom::num(1);
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ((ltq!(m_, -1) && !igtq!(m_p_1, 0))
                    || (ltq!(m_, 0) && ltq!(p_, -1))
                    || eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0))
                && neq!(&m_ + &p_ + Atom::num(1), 0)
        },
        rhs: {
            let m_p_1 = &m_ + &p_ + Atom::num(1);
            let p_plus_one = &p_ + Atom::num(1);
            let linear_factor = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct_denominator = &linear_factor * &m_p_1;
            let recursive_denominator = &e__ * &linear_factor * &m_p_1;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_coefficient = &d__ * &g__ - &e__ * &f__;
            let recursive_coefficient = &m_ * (&g__ * (&c__ * &d__ - &b__ * &e__) + &c__ * &e__ * &f__)
                + &e__ * &p_plus_one * (Atom::num(2) * &c__ * &f__ - &b__ * &g__);
            let recursive_integrand = linear.pow(&m_ + Atom::num(1)) * trinomial.pow(&p_);
            rubi_simp(&(direct_coefficient * linear.pow(&m_) * trinomial.pow(&p_plus_one) / direct_denominator), x_)
                    + rubi_star(recursive_coefficient / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1221,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) +
          (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*e*(m+2*p+2)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && NeQ[m+2*p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            let shifted = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(shifted, 0)
        },
        rhs: {
            let shifted = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let p_plus_one = &p_ + Atom::num(1);
            let direct_denominator = &c__ * &shifted;
            let recursive_denominator = &c__ * &e__ * &shifted;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_coefficient = &m_ * (&g__ * (&c__ * &d__ - &b__ * &e__) + &c__ * &e__ * &f__)
                + &e__ * &p_plus_one * (Atom::num(2) * &c__ * &f__ - &b__ * &g__);
            let recursive_integrand = linear.pow(&m_) * trinomial.pow(&p_);
            rubi_simp(&(&g__ * linear.pow(&m_) * trinomial.pow(&p_plus_one) / direct_denominator), x_)
                    + rubi_star(recursive_coefficient / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1226,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[Simplify[m+2*p+3],0] && EqQ[b*(e*f+d*g)-2*(c*d*f+a*e*g),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && eqq!(
                    &b__ * (&e__ * &f__ + &d__ * &g__) - Atom::num(2) * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__),
                    0
                )
        },
        rhs: {
            let p_plus_one = &p_ + Atom::num(1);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = Atom::num(2) * &p_plus_one * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);

            rubi_simp(&(-(&e__ * &f__ - &d__ * &g__) * linear.pow(&m_ + Atom::num(1)) * trinomial.pow(&p_plus_one)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1227,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(b*f-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) -
          m*(b*(e*f+d*g)-2*(c*d*f+a*e*g))/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[Simplify[m+2*p+3],0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let p_plus_one = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &p_plus_one * &discriminant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor =
                &b__ * &f__ - Atom::num(2) * &a__ * &g__ + (Atom::num(2) * &c__ * &f__ - &b__ * &g__) * x_;
            let recursive_coefficient =
                &m_ * (&b__ * (&e__ * &f__ + &d__ * &g__) - Atom::num(2) * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__));
            let recursive_integrand = linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_plus_one);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear.pow(&m_) * trinomial.pow(&p_plus_one) * direct_factor / &denominator), x_)
                    - rubi_star(recursive_coefficient / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1228,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) -
          (b*(e*f+d*g)-2*(c*d*f+a*e*g))/(2*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[Simplify[m+2*p+3],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
        },
        rhs: {
            let p_plus_one = &p_ + Atom::num(1);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let direct_denominator = Atom::num(2) * &p_plus_one * &invariant;
            let recursive_denominator = Atom::num(2) * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_coefficient =
                &b__ * (&e__ * &f__ + &d__ * &g__) - Atom::num(2) * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__);
            let recursive_integrand = linear.pow(&m_ + Atom::num(1)) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-(&e__ * &f__ - &d__ * &g__) * linear.pow(&m_ + Atom::num(1)) * trinomial.pow(&p_plus_one)
                    / direct_denominator), x_)
                    - rubi_star(recursive_coefficient / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1229,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2))*
            ((d*g-e*f*(m+2))*(c*d^2-b*d*e+a*e^2)-d*p*(2*c*d-b*e)*(e*f-d*g)-e*(g*(m+1)*(c*d^2-b*d*e+a*e^2)+p*(2*c*d-b*e)*(e*f-d*g))*x) -
          p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1)*
            Simp[2*a*c*e*(e*f-d*g)*(m+2)+b^2*e*(d*g*(p+1)-e*f*(m+p+2))+b*(a*e^2*g*(m+1)-c*d*(d*g*(2*p+1)-e*f*(m+2*p+2)))-
              c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-e*(2*a*e*g*(m+1)-b*(d*g*(m-2*p)+e*f*(m+2*p+2))))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && GtQ[p,0] && LtQ[m,-2] && LtQ[m+2*p,0] && Not[ILtQ[m+2*p+3,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -2)
                && ltq!(&m_ + Atom::num(2) * &p_, 0)
                && !iltq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
        },
        rhs: {
            let m_plus_one = &m_ + Atom::num(1);
            let m_plus_two = &m_ + Atom::num(2);
            let p_plus_one = &p_ + Atom::num(1);
            let p_minus_one = &p_ - Atom::num(1);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let balance = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let denominator = e__.pow(2) * &m_plus_one * &m_plus_two * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = (&d__ * &g__ - &e__ * &f__ * &m_plus_two) * &invariant
                - &d__ * &p_ * &balance * &ef_dg
                - &e__ * (&g__ * &m_plus_one * &invariant + &p_ * &balance * &ef_dg) * x_;
            let simp = rubi_simp(
                &(Atom::num(2) * &a__ * &c__ * &e__ * &ef_dg * &m_plus_two
                    + b__.pow(2) * &e__ * (&d__ * &g__ * &p_plus_one - &e__ * &f__ * (&m_ + &p_ + Atom::num(2)))
                    + &b__
                        * (&a__ * e__.pow(2) * &g__ * &m_plus_one
                            - &c__
                                * &d__
                                * (&d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(1))
                                    - &e__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2))))
                    - &c__
                        * (Atom::num(2)
                            * &c__
                            * &d__
                            * (&d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(1))
                                - &e__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2)))
                            - &e__
                                * (Atom::num(2) * &a__ * &e__ * &g__ * &m_plus_one
                                    - &b__
                                        * (&d__ * &g__ * (&m_ - Atom::num(2) * &p_)
                                            + &e__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2)))))
                        * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_two) * trinomial.pow(&p_minus_one) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-linear.pow(&m_plus_one) * trinomial.pow(&p_) * direct_factor / &denominator), x_)
                    - rubi_star(&p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1230,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) +
          p/(e^2*(m+1)*(m+2*p+2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1)*
            Simp[g*(b*d+2*a*e+2*a*e*m+2*b*d*p)-f*b*e*(m+2*p+2)+(g*(2*c*d+b*e+b*e*m+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && GtQ[p,0] &&
          (LtQ[m,-1] || EqQ[p,1] || IntegerQ[p] && Not[RationalQ[m]]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            let m_2p_1 = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && gtq!(p_, 0)
                && (ltq!(m_, -1) || eqq!(p_, 1) || integerq!(p_) && !rationalq!(m_))
                && neq!(m_, -1)
                && !iltq!(m_2p_1, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let m_plus_one = &m_ + Atom::num(1);
            let m_2p_2 = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let p_minus_one = &p_ - Atom::num(1);
            let denominator = e__.pow(2) * &m_plus_one * &m_2p_2;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = &e__ * &f__ * &m_2p_2
                - &d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(1))
                + &e__ * &g__ * &m_plus_one * x_;
            let simp = rubi_simp(
                &(&g__
                    * (&b__ * &d__
                        + Atom::num(2) * &a__ * &e__
                        + Atom::num(2) * &a__ * &e__ * &m_
                        + Atom::num(2) * &b__ * &d__ * &p_)
                    - &f__ * &b__ * &e__ * &m_2p_2
                    + (&g__
                        * (Atom::num(2) * &c__ * &d__
                            + &b__ * &e__
                            + &b__ * &e__ * &m_
                            + Atom::num(4) * &c__ * &d__ * &p_)
                        - Atom::num(2) * &c__ * &e__ * &f__ * &m_2p_2)
                        * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_one) * trinomial.pow(&p_minus_one) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear.pow(&m_plus_one) * direct_factor * trinomial.pow(&p_) / &denominator), x_)
                    + rubi_star(&p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1231,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*(c*d+2*c*d*p-b*e*p)+g*c*e*(m+2*p+1)*x)*(a+b*x+c*x^2)^p/
            (c*e^2*(m+2*p+1)*(m+2*p+2)) -
          p/(c*e^2*(m+2*p+1)*(m+2*p+2)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1)*
            Simp[c*e*f*(b*d-2*a*e)*(m+2*p+2)+g*(a*e*(b*e-2*c*d*m+b*e*m)+b*d*(b*e*p-c*d-2*c*d*p))+
              (c*e*f*(2*c*d-b*e)*(m+2*p+2)+g*(b^2*e^2*(p+m+1)-2*c^2*d^2*(1+2*p)-c*e*(b*d*(m-2*p)+2*a*e*(m+2*p+1))))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] &&
          GtQ[p,0] && (IntegerQ[p] || Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,0]) && Not[ILtQ[m+2*p,0]] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            let m_2p = &m_ + Atom::num(2) * &p_;
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && gtq!(p_, 0)
                && (integerq!(p_) || !rationalq!(m_) || geq!(m_, -1) && ltq!(m_, 0))
                && !iltq!(m_2p, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let m_2p_1 = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let m_2p_2 = &m_ + Atom::num(2) * &p_ + Atom::num(2);
            let p_minus_one = &p_ - Atom::num(1);
            let denominator = &c__ * e__.pow(2) * &m_2p_1 * &m_2p_2;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = &c__ * &e__ * &f__ * &m_2p_2
                - &g__ * (&c__ * &d__ + Atom::num(2) * &c__ * &d__ * &p_ - &b__ * &e__ * &p_)
                + &g__ * &c__ * &e__ * &m_2p_1 * x_;
            let simp = rubi_simp(
                &(&c__ * &e__ * &f__ * (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * &m_2p_2
                    + &g__
                        * (&a__ * &e__ * (&b__ * &e__ - Atom::num(2) * &c__ * &d__ * &m_ + &b__ * &e__ * &m_)
                            + &b__ * &d__ * (&b__ * &e__ * &p_ - &c__ * &d__ - Atom::num(2) * &c__ * &d__ * &p_))
                    + (&c__ * &e__ * &f__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * &m_2p_2
                        + &g__
                            * (b__.pow(2) * e__.pow(2) * (&p_ + &m_ + Atom::num(1))
                                - Atom::num(2) * c__.pow(2) * d__.pow(2) * (Atom::num(1) + Atom::num(2) * &p_)
                                - &c__
                                    * &e__
                                    * (&b__ * &d__ * (&m_ - Atom::num(2) * &p_)
                                        + Atom::num(2) * &a__ * &e__ * &m_2p_1)))
                        * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_) * trinomial.pow(&p_minus_one) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * direct_factor * trinomial.pow(&p_) / &denominator), x_)
                    - rubi_star(&p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1232,
        source: "Int[(d_+e_.*x_)^m_*(f_+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(a+b*x+c*x^2)^p*ExpandIntegrand[(d+e*x)^m*(f+g*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && ILtQ[p,-1] && IGtQ[m,0] && RationalQ[a,b,c,d,e,f,g]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, e__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && iltq!(p_, -1)
                && igtq!(m_, 0)
                && rationalq!([a__, b__, c__, d__, e__, f__, g__])
        },
        rhs: {
            let linear_factor = (&d__ + &e__ * x_).pow(&m_) * (&f__ + &g__ * x_);
            let expanded = rubi_expand_integrand(&linear_factor, x_);
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_) * expanded;

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1233,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          -(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(2*c^2*d*f+b^2*e*g-c*(b*e*f+b*d*g+2*a*e*g))*x)/
            (c*(p+1)*(b^2-4*a*c)) -
          1/(c*(p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1)*
            Simp[2*c^2*d^2*f*(2*p+3)+b*e*g*(a*e*(m-1)+b*d*(p+2))-c*(2*a*e*(e*f*(m-1)+d*g*m)+b*d*(d*g*(2*p+3)-e*f*(m-2*p-4))) +
              e*(b^2*e*g*(m+p+1)+2*c^2*d*f*(m+2*p+2)-c*(2*a*e*g*m+b*(e*f+d*g)*(m+2*p+2)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && LtQ[p,-1] && GtQ[m,1] &&
          (EqQ[m,2] && EqQ[p,-3] && RationalQ[a,b,c,d,e,f,g] || Not[ILtQ[m+2*p+3,0]])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            let m_2p_3 = &m_ + Atom::num(2) * &p_ + Atom::num(3);
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && (eqq!(m_, 2) && eqq!(p_, -3) && rationalq!([a__, b__, c__, d__, e__, f__, g__])
                    || !iltq!(m_2p_3, 0))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &c__ * (&p_ + Atom::num(1)) * &discriminant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = Atom::num(2) * &a__ * &c__ * (&e__ * &f__ + &d__ * &g__)
                - &b__ * (&c__ * &d__ * &f__ + &a__ * &e__ * &g__)
                - (Atom::num(2) * c__.pow(2) * &d__ * &f__ + b__.pow(2) * &e__ * &g__
                    - &c__ * (&b__ * &e__ * &f__ + &b__ * &d__ * &g__ + Atom::num(2) * &a__ * &e__ * &g__))
                    * x_;
            let simp = rubi_simp(
                &(Atom::num(2) * c__.pow(2) * d__.pow(2) * &f__ * (Atom::num(2) * &p_ + Atom::num(3))
                    + &b__ * &e__ * &g__ * (&a__ * &e__ * (&m_ - Atom::num(1)) + &b__ * &d__ * (&p_ + Atom::num(2)))
                    - &c__
                        * (Atom::num(2) * &a__ * &e__ * (&e__ * &f__ * (&m_ - Atom::num(1)) + &d__ * &g__ * &m_)
                            + &b__ * &d__ * (&d__ * &g__ * (Atom::num(2) * &p_ + Atom::num(3)) - &e__ * &f__ * (&m_ - Atom::num(2) * &p_ - Atom::num(4))))
                    + &e__
                        * (b__.pow(2) * &e__ * &g__ * (&m_ + &p_ + Atom::num(1))
                            + Atom::num(2) * c__.pow(2) * &d__ * &f__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2))
                            - &c__
                                * (Atom::num(2) * &a__ * &e__ * &g__ * &m_
                                    + &b__ * (&e__ * &f__ + &d__ * &g__) * (&m_ + Atom::num(2) * &p_ + Atom::num(2))))
                        * x_),
                x_,
            );
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(2)) * trinomial.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_ + Atom::num(1)) * direct_factor / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1234,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(f*b-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
            Simp[g*(2*a*e*m+b*d*(2*p+3))-f*(b*e*m+2*c*d*(2*p+3))-e*(2*c*f-b*g)*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && LtQ[p,-1] && GtQ[m,0] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = (&p_ + Atom::num(1)) * &discriminant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = &f__ * &b__ - Atom::num(2) * &a__ * &g__
                + (Atom::num(2) * &c__ * &f__ - &b__ * &g__) * x_;
            let simp = rubi_simp(
                &(&g__ * (Atom::num(2) * &a__ * &e__ * &m_ + &b__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3)))
                    - &f__ * (&b__ * &e__ * &m_ + Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3)))
                    - &e__ * (Atom::num(2) * &c__ * &f__ - &b__ * &g__) * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_),
                x_,
            );
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear.pow(&m_) * trinomial.pow(&p_ + Atom::num(1)) * direct_factor / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1235,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^(m+1)*(f*(b*c*d-b^2*e+2*a*c*e)-a*g*(2*c*d-b*e)+c*(f*(2*c*d-b*e)-g*(b*d-2*a*e))*x)*(a+b*x+c*x^2)^(p+1)/
            ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) +
          1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
            Simp[f*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
              g*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
              c*e*(g*(b*d-2*a*e)-f*(2*c*d-b*e))*(m+2*p+4)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && LtQ[p,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && ltq!(p_, -1)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&p_ + Atom::num(1)) * &discriminant * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct_factor = &f__ * (&b__ * &c__ * &d__ - b__.pow(2) * &e__ + Atom::num(2) * &a__ * &c__ * &e__)
                - &a__ * &g__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                + &c__ * (&f__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) - &g__ * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)) * x_;
            let simp = rubi_simp(
                &(&f__
                    * (&b__ * &c__ * &d__ * &e__ * (Atom::num(2) * &p_ - &m_ + Atom::num(2))
                        + b__.pow(2) * e__.pow(2) * (&p_ + &m_ + Atom::num(2))
                        - Atom::num(2) * c__.pow(2) * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(3))
                        - Atom::num(2) * &a__ * &c__ * e__.pow(2) * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                    - &g__
                        * (&a__ * &e__ * (&b__ * &e__ - Atom::num(2) * &c__ * &d__ * &m_ + &b__ * &e__ * &m_)
                            - &b__ * &d__ * (Atom::num(3) * &c__ * &d__ - &b__ * &e__ + Atom::num(2) * &c__ * &d__ * &p_ - &b__ * &e__ * &p_))
                    + &c__ * &e__ * (&g__ * (&b__ * &d__ - Atom::num(2) * &a__ * &e__) - &f__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__))
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                        * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_) * trinomial.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let direct = linear.pow(&m_ + Atom::num(1))
                * direct_factor
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1196,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          g*(d+e*x)^m/(c*m) +
          1/c \\[Star] Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d-b*e*g+c*e*f)*x,x]/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && FractionQ[m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && fractionq!(m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let c_m = &c__ * &m_;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let simp = rubi_simp(
                &(&c__ * &d__ * &f__ - &a__ * &e__ * &g__
                    + (&g__ * &c__ * &d__ - &b__ * &e__ * &g__ + &c__ * &e__ * &f__) * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_ - Atom::num(1)) * simp / trinomial;
            rubi_simp(&(&g__ * linear.pow(&m_) / c_m), x_)
                    + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1197,
        source: "Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
          2 \\[Star] Subst[Int[(e*f-d*g+g*x^2)/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_) / ((d__ + e__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2))),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2)
                - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * sub_atom.pow(2)
                + &c__ * sub_atom.pow(4);
            let transformed_numerator = &e__ * &f__ - &d__ * &g__ + &g__ * sub_atom.pow(2);
            let transformed = rubi_rhs_int(
                &(transformed_numerator / transformed_denominator),
                sub_symbol,
            );

            let substitution = (&d__ + &e__ * x_).sqrt();

            rubi_star(Atom::num(2), rubi_subst(&transformed, sub_symbol, substitution))
        },
    ));
}

fn push_rules_rule_1198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1198,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x)^(m+1)*Simp[c*d*f-f*b*e+a*e*g-c*(e*f-d*g)*x,x]/(a+b*x+c*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && FractionQ[m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && fractionq!(m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let direct_denominator = &m_plus_one * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let simp = rubi_simp(
                &(&c__ * &d__ * &f__ - &f__ * &b__ * &e__ + &a__ * &e__ * &g__ - &c__ * &ef_dg * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_one) * simp / trinomial;
            rubi_simp(&(ef_dg * linear.pow(m_plus_one) / direct_denominator), x_)
                    + rubi_star(Atom::num(1) / invariant, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1236,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) +
          1/(c*(m+2*p+2)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p*
            Simp[m*(c*d*f-a*e*g)+d*(2*c*f-b*g)*(p+1)+(m*(c*e*f+c*d*g-b*e*g)+e*(p+1)*(2*c*f-b*g))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && GtQ[m,0] && NeQ[m+2*p+2,0] &&
          (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p]) && Not[IGtQ[m,0] && EqQ[f,0]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && gtq!(m_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(2), 0)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
                && !(igtq!(m_, 0) && eqq!(f__, 0))
        },
        rhs: {
            let denominator = &c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(2));
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let p_plus_one = &p_ + Atom::num(1);
            let simp = rubi_simp(
                &(&m_ * (&c__ * &d__ * &f__ - &a__ * &e__ * &g__)
                    + &d__ * (Atom::num(2) * &c__ * &f__ - &b__ * &g__) * &p_plus_one
                    + (&m_ * (&c__ * &e__ * &f__ + &c__ * &d__ * &g__ - &b__ * &e__ * &g__)
                        + &e__ * &p_plus_one * (Atom::num(2) * &c__ * &f__ - &b__ * &g__))
                        * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_ - Atom::num(1)) * trinomial.pow(&p_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * linear.pow(&m_) * trinomial.pow(p_plus_one) / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1237,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
            Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && LtQ[m,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && ltq!(m_, -1)
                && (integerq!(m_)
                    || integerq!(p_)
                    || integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]))
        },
        rhs: {
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let denominator = &m_plus_one * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let simp = rubi_simp(
                &((&c__ * &d__ * &f__ - &f__ * &b__ * &e__ + &a__ * &e__ * &g__) * &m_plus_one
                    + &b__ * (&d__ * &g__ - &e__ * &f__) * (&p_ + Atom::num(1))
                    - &c__ * &ef_dg * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_one) * trinomial.pow(&p_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(ef_dg * linear.pow(m_plus_one) * trinomial.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1238,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
            Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && ILtQ[Simplify[m+2*p+3],0] && NeQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && iltq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + Atom::num(3))), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let denominator = &m_plus_one * &invariant;
            let linear = &d__ + &e__ * x_;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_dg = &e__ * &f__ - &d__ * &g__;
            let simp = rubi_simp(
                &((&c__ * &d__ * &f__ - &f__ * &b__ * &e__ + &a__ * &e__ * &g__) * &m_plus_one
                    + &b__ * (&d__ * &g__ - &e__ * &f__) * (&p_ + Atom::num(1))
                    - &c__ * &ef_dg * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_),
                x_,
            );
            let recursive_integrand = linear.pow(&m_plus_one) * trinomial.pow(&p_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(ef_dg * linear.pow(m_plus_one) * trinomial.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1239,
        source: "Int[(f_+g_.*x_)/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          4*f*(a-d)/(b*d-a*e) \\[Star] Subst[Int[1/(4*(a-d)-x^2),x],x,(2*(a-d)+(b-e)*x)/Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[4*c*(a-d)-(b-e)^2,0] && EqQ[e*f*(b-e)-2*g*(b*d-a*e),0] && NeQ[b*d-a*e,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_) / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, g__],
        when: {
            let determinant = &b__ * &d__ - &a__ * &e__;
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(Atom::num(4) * &c__ * (&a__ - &d__) - (&b__ - &e__).pow(2), 0)
                && eqq!(&e__ * &f__ * (&b__ - &e__) - Atom::num(2) * &g__ * &determinant, 0)
                && neq!(determinant, 0)
        },
        rhs: {
            let determinant = &b__ * &d__ - &a__ * &e__;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(4) * (&a__ - &d__) - sub_atom.pow(2))),
                sub_symbol,
            );

            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let substitution =
                (Atom::num(2) * (&a__ - &d__) + (&b__ - &e__) * x_) / trinomial.sqrt();
            let substituted = rubi_subst(&transformed, sub_symbol, substitution);

            rubi_star(Atom::num(4) * &f__ * (&a__ - &d__) / determinant, substituted)
        },
    ));
}

fn push_rules_rule_1240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1240,
        source: "Int[(f_+g_.*x_)/(Sqrt[x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
          2 \\[Star] Subst[Int[(f+g*x^2)/Sqrt[a+b*x^2+c*x^4],x],x,Sqrt[x]] /;
        FreeQ[{a,b,c,f,g},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_)
            / (x_.pow(Atom::num(1) / Atom::num(2)) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, f__, g__, x_],
        optional: [b__, c__, g__],
        when: { freeq!([a__, b__, c__, f__, g__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = (&f__ + &g__ * sub_atom.pow(2))
                / (&a__ + &b__ * sub_atom.pow(2) + &c__ * sub_atom.pow(4)).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.sqrt());

            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1241,
        source: "Int[(f_+g_.*x_)/(Sqrt[e_*x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
          Sqrt[x]/Sqrt[e*x] \\[Star] Int[(f+g*x)/(Sqrt[x]*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,e,f,g},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ + g__ * x_)
            / ((e__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, e__, f__, g__, x_],
        optional: [b__, c__, g__],
        when: { freeq!([a__, b__, c__, e__, f__, g__], x_) },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = (&f__ + &g__ * x_)
                / (x_.sqrt() * quadratic.sqrt());
            rubi_star(x_.sqrt() / (&e__ * x_).sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1242,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a*e+c*d*x,x], R=PolynomialRemainder[(f+g*x)^n,a*e+c*d*x,x]},
          R*(2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[d*e*(p+1)*(b^2-4*a*c)*Q-R*(2*c*d-b*e)*(m+2*p+2),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,1] && IGtQ[m,0] && LtQ[p,-1] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && igtq!(m_, 0)
                && ltq!(p_, -1)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let second_power = (&f__ + &g__ * x_).pow(&n_);
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let divisor = &a__ * &e__ + &c__ * &d__ * x_;
            let capital_q = rubi_polynomial_quotient(&second_power, &divisor, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&second_power, &divisor, x_).rubi_rhs();
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let balance = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let p_plus_one = &p_ + Atom::num(1);
            let denominator = &p_plus_one * &discriminant;
            let direct = &capital_r
                * &balance
                * linear.pow(&m_)
                * quadratic.pow(&p_plus_one)
                / (&e__ * &denominator);
            let payload = rubi_expand_to_sum(
                &(&d__ * &e__ * &p_plus_one * &discriminant * capital_q
                    - &capital_r
                        * &balance
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(2))),
                x_,
            );
            let recursive_integrand =
                linear.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_plus_one) * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1243,
        source: "Int[(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          -(2*c*d-b*e)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(e*p*(b^2-4*a*c)*(d+e*x)) +
          n*(a*g*(2*c*d-b*e)-c*f*(b*d-2*a*e))/(d*e*p*(b^2-4*a*c)) \\[Star] Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[n,1] && LtQ[p,-1] && EqQ[n+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && eqq!(&n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &d__ + &e__ * x_;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let balance = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct = -&balance * second.pow(&n_) * quadratic.pow(&p_ + Atom::num(1))
                / (&e__ * &p_ * &discriminant * linear);
            let coefficient = &n_
                * (&a__ * &g__ * &balance
                    - &c__ * &f__ * (&b__ * &d__ - Atom::num(2) * &a__ * &e__))
                / (&d__ * &e__ * &p_ * &discriminant);
            let recursive_integrand =
                second.pow(&n_ - Atom::num(1)) * quadratic.pow(&p_);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1244,
        source: "Int[(f_.+g_.*x_)^n_*(a_+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          -(e*f-d*g)*(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1)/(p*(2*c*d-b*e)*(d+e*x)) +
          1/(p*e^2*(2*c*d-b*e)) \\[Star] Int[(f+g*x)^(n-2)*(a+b*x+c*x^2)^p*
            Simp[b*e*g*(-e*f+d*g+e*f*n-d*g*n-e*f*p)+c*(d^2*g^2*(n-1)-d*e*f*g*n+e^2*f^2*(2*p+1))-e*g*(b*e*g*p-c*(e*f*n-d*g*n+2*e*f*p))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let linear = &d__ + &e__ * x_;
            let balance = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct = -(&e__ * &f__ - &d__ * &g__)
                * second.pow(&n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&p_ * &balance * linear);
            let payload = rubi_simp(
                &(&b__
                    * &e__
                    * &g__
                    * (-&e__ * &f__ + &d__ * &g__ + &e__ * &f__ * &n_
                        - &d__ * &g__ * &n_
                        - &e__ * &f__ * &p_)
                    + &c__
                        * (d__.pow(2) * g__.pow(2) * (&n_ - Atom::num(1))
                            - &d__ * &e__ * &f__ * &g__ * &n_
                            + e__.pow(2) * f__.pow(2) * (Atom::num(2) * &p_ + Atom::num(1)))
                    - &e__
                        * &g__
                        * (&b__ * &e__ * &g__ * &p_
                            - &c__
                                * (&e__ * &f__ * &n_ - &d__ * &g__ * &n_
                                    + Atom::num(2) * &e__ * &f__ * &p_))
                        * x_),
                x_,
            );
            let recursive_integrand = second.pow(&n_ - Atom::num(2))
                * quadratic.pow(&p_)
                * payload;
            let coefficient = Atom::num(1) / (&p_ * e__.pow(2) * &balance);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1245,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[a,0] && GtQ[d,0] && LtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && gtq!(a__, 0)
                && gtq!(d__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let recursive_integrand = (&d__ + &e__ * x_).pow(&m_ + &p_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ / &d__ + &c__ * x_ / &e__).pow(&p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1246,
        source: "Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
          (f+g*x)^(n+1)*(a+b*x+c*x^2)^p*(c*d-b*e-c*e*x)/(p*(2*c*d-b*e)*(e*f-d*g)) +
          1/(p*(2*c*d-b*e)*(e*f-d*g)) \\[Star] Int[(f+g*x)^n*(a+b*x+c*x^2)^p*(b*e*g*(n+p+1)+c*e*f*(2*p+1)-c*d*g*(n+2*p+1)+c*e*g*(n+2*p+2)*x),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[n,0] && ILtQ[n+2*p,0] && Not[IGtQ[n,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(n_, 0)
                && iltq!(&n_ + Atom::num(2) * &p_, 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &p_
                * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                * (&e__ * &f__ - &d__ * &g__);
            let direct = second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_)
                * (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)
                / &denominator;
            let payload = &b__ * &e__ * &g__ * (&n_ + &p_ + Atom::num(1))
                + &c__ * &e__ * &f__ * (Atom::num(2) * &p_ + Atom::num(1))
                - &c__ * &d__ * &g__ * (&n_ + Atom::num(2) * &p_ + Atom::num(1))
                + &c__
                    * &e__
                    * &g__
                    * (&n_ + Atom::num(2) * &p_ + Atom::num(2))
                    * x_;
            let recursive_integrand = second.pow(&n_) * quadratic.pow(&p_) * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1247,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && EqQ[c*e*f+c*d*g-b*e*g,0] && NeQ[m-n-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && eqq!(&c__ * &e__ * &f__ + &c__ * &d__ * &g__ - &b__ * &e__ * &g__, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
        },
        rhs: {
            rubi_simp(&(-&e__
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(1))
                    * (&f__ + &g__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / (&c__ * (&m_ - &n_ - Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_1248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1248,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && EqQ[m-n-2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && eqq!(&m_ - &n_ - Atom::num(2), 0)
        },
        rhs: {
            rubi_simp(&(-e__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(1))
                    * (&f__ + &g__ * x_).pow(&n_ + Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / ((&n_ + Atom::num(1))
                        * (&c__ * &e__ * &f__ + &c__ * &d__ * &g__
                            - &b__ * &e__ * &g__))), x_)
        },
    ));
}

fn push_rules_rule_1249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1249,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(n+1)) +
          c*m/(e*g*(n+1)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && GtQ[p,0] && LtQ[n,-1] && Not[IntegerQ[n+p] && LeQ[n+p+2,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(p_, 0)
                && ltq!(n_, -1)
                && !(integerq!(&n_ + &p_)
                    && leq!(&n_ + &p_ + Atom::num(2), 0))
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = first.pow(&m_)
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_)
                / (&g__ * (&n_ + Atom::num(1)));
            let recursive_integrand = first.pow(&m_ + Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ - Atom::num(1));
            rubi_simp(&(direct), x_)
                    + rubi_star(&c__ * &m_ / (&e__ * &g__ * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1250,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(m-n-1)) -
          m*(c*e*f+c*d*g-b*e*g)/(e^2*g*(m-n-1)) \\[Star] Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && GtQ[p,0] && NeQ[m-n-1,0] && Not[IGtQ[n,0]] && Not[IntegerQ[n+p] && LtQ[n+p+2,0]] && RationalQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
                && !igtq!(n_, 0)
                && !(integerq!(&n_ + &p_)
                    && ltq!(&n_ + &p_ + Atom::num(2), 0))
                && rationalq!(n_)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ - &n_ - Atom::num(1);
            let direct = -first.pow(&m_)
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_)
                / (&g__ * &balance);
            let recursive_integrand = first.pow(&m_ + Atom::num(1))
                * second.pow(&n_)
                * quadratic.pow(&p_ - Atom::num(1));
            let coefficient = &m_
                * (&c__ * &e__ * &f__ + &c__ * &d__ * &g__
                    - &b__ * &e__ * &g__)
                / (e__.pow(2) * &g__ * &balance);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1251,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) -
          e*g*n/(c*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && LtQ[p,-1] && GtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let p_plus_one = &p_ + Atom::num(1);
            let direct = &e__
                * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_)
                * quadratic.pow(&p_plus_one)
                / (&c__ * &p_plus_one);
            let recursive_integrand = first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ - Atom::num(1))
                * quadratic.pow(&p_plus_one);
            rubi_simp(&(direct), x_)
                    - rubi_star(&e__ * &g__ * &n_ / (&c__ * &p_plus_one), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1252,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(c*e*f+c*d*g-b*e*g)) +
          e^2*g*(m-n-2)/((p+1)*(c*e*f+c*d*g-b*e*g)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && LtQ[p,-1] && RationalQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(p_, -1)
                && rationalq!(n_)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let p_plus_one = &p_ + Atom::num(1);
            let invariant = &c__ * &e__ * &f__ + &c__ * &d__ * &g__
                - &b__ * &e__ * &g__;
            let direct = e__.pow(2)
                * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_plus_one)
                / (&p_plus_one * &invariant);
            let recursive_integrand = first.pow(&m_ - Atom::num(1))
                * second.pow(&n_)
                * quadratic.pow(&p_plus_one);
            let coefficient = e__.pow(2) * &g__ * (&m_ - &n_ - Atom::num(2))
                / (&p_plus_one * &invariant);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1253,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) -
          n*(c*e*f+c*d*g-b*e*g)/(c*e*(m-n-1)) \\[Star] Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && GtQ[n,0] && NeQ[m-n-1,0] && (IntegerQ[2*p] || IntegerQ[n])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && gtq!(n_, 0)
                && neq!(&m_ - &n_ - Atom::num(1), 0)
                && (integerq!(Atom::num(2) * &p_) || integerq!(n_))
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ - &n_ - Atom::num(1);
            let direct = -&e__
                * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_)
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * &balance);
            let recursive_integrand = first.pow(&m_)
                * second.pow(&n_ - Atom::num(1))
                * quadratic.pow(&p_);
            let coefficient = &n_
                * (&c__ * &e__ * &f__ + &c__ * &d__ * &g__
                    - &b__ * &e__ * &g__)
                / (&c__ * &e__ * &balance);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1254,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) -
          c*e*(m-n-2)/((n+1)*(c*e*f+c*d*g-b*e*g)) \\[Star] Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p,0] && LtQ[n,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_, 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * &e__ * &f__ + &c__ * &d__ * &g__
                - &b__ * &e__ * &g__;
            let direct = -e__.pow(2)
                * first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / ((&n_ + Atom::num(1)) * &invariant);
            let recursive_integrand = first.pow(&m_)
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_);
            let coefficient = &c__
                * &e__
                * (&m_ - &n_ - Atom::num(2))
                / ((&n_ + Atom::num(1)) * &invariant);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1255,
        source: "Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          2*e^2 \\[Star] Subst[Int[1/(c*(e*f+d*g)-b*e*g+e^2*g*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt()
            / ((f__ + g__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / (&c__ * (&e__ * &f__ + &d__ * &g__) - &b__ * &e__ * &g__
                    + e__.pow(2) * &g__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substitution = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_).sqrt();
            let substituted = rubi_subst(&transformed, sub_symbol, substitution);
            rubi_star(Atom::num(2) * e__.pow(2), substituted)
        },
    ));
}

fn push_rules_rule_1256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1256,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p-1,0] && EqQ[b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3),0] && NeQ[n+p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            let balance = &b__ * &e__ * &g__ * (&n_ + Atom::num(1))
                + &c__ * &e__ * &f__ * (&p_ + Atom::num(1))
                - &c__ * &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3));
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && eqq!(balance, 0)
                && neq!(&n_ + &p_ + Atom::num(2), 0)
        },
        rhs: {
            rubi_simp(&(e__.pow(2)
                    * (&d__ + &e__ * x_).pow(&m_ - Atom::num(2))
                    * (&f__ + &g__ * x_).pow(&n_ + Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2))
                        .pow(&p_ + Atom::num(1))
                    / (&c__ * &g__ * (&n_ + &p_ + Atom::num(2)))), x_)
        },
    ));
}

fn push_rules_rule_1257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1257,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(g*(n+1)*(c*e*f+c*d*g-b*e*g)) -
          e*(b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(g*(n+1)*(c*e*f+c*d*g-b*e*g)) \\[Star]
            Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p-1,0] && LtQ[n,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * &e__ * &f__ + &c__ * &d__ * &g__
                - &b__ * &e__ * &g__;
            let balance = &b__ * &e__ * &g__ * (&n_ + Atom::num(1))
                + &c__ * &e__ * &f__ * (&p_ + Atom::num(1))
                - &c__ * &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3));
            let denominator = &g__ * (&n_ + Atom::num(1)) * &invariant;
            let direct = e__.pow(2)
                * (&e__ * &f__ - &d__ * &g__)
                * first.pow(&m_ - Atom::num(2))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = first.pow(&m_ - Atom::num(1))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(&e__ * balance / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1258,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) -
          (b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(c*g*(n+p+2)) \\[Star] Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+p-1,0] && Not[LtQ[n,-1]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &p_ - Atom::num(1), 0)
                && !ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &b__ * &e__ * &g__ * (&n_ + Atom::num(1))
                + &c__ * &e__ * &f__ * (&p_ + Atom::num(1))
                - &c__ * &d__ * &g__ * (Atom::num(2) * &n_ + &p_ + Atom::num(3));
            let denominator = &c__ * &g__ * (&n_ + &p_ + Atom::num(2));
            let direct = e__.pow(2)
                * first.pow(&m_ - Atom::num(2))
                * second.pow(&n_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = first.pow(&m_ - Atom::num(1))
                * second.pow(&n_)
                * quadratic.pow(&p_);
            rubi_simp(&(direct), x_)
                    - rubi_star(balance / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1259,
        source: "Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[m,0] && (ILtQ[n,0] || IGtQ[n,0] && ILtQ[p+1/2,0]) && Not[IGtQ[n,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(m_, 0)
                && (iltq!(n_, 0)
                    || igtq!(n_, 0) && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0))
                && !igtq!(n_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1260,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x+c*x^2)^p,(d+e*x)^m*(f+g*x)^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+n+2*p+1,0] && ILtQ[m,0] && ILtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && iltq!(m_, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let quadratic = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let affine_product = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_);
            let expanded = rubi_expand_integrand_product(&quadratic, &affine_product, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1261,
        source: "Int[(e_.*x_)^m_*(f_.+g_.*x_)^n_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p) \\[Star] Int[x^(m+p)*(f+g*x)^n*(b+c*x)^p,x] /;
        FreeQ[{b,c,e,f,g,m,n},x] && Not[IGtQ[n,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            * (f__ + g__ * x_).pow(n_)
            * (b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [b__, c__, e__, f__, g__, m_, n_, p_, x_],
        optional: [b__, c__, e__, f__, g__],
        when: {
            freeq!([b__, c__, e__, f__, g__, m_, n_], x_) && !igtq!(n_, 0)
        },
        rhs: {
            let quadratic = &b__ * x_ + &c__ * x_.pow(2);
            let linear = &b__ + &c__ * x_;
            let m_plus_p = &m_ + &p_;
            let prefactor = (&e__ * x_).pow(&m_) * quadratic.pow(&p_)
                / (x_.pow(&m_plus_p) * linear.pow(&p_));
            let recursive_integrand = x_.pow(m_plus_p)
                * (&f__ + &g__ * x_).pow(&n_)
                * linear.pow(&p_);
            rubi_star(prefactor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1262,
        source: "Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
            ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n+e*g^n*(m+p+n)*(d+e*x)^(n-2)*(b*d-2*a*e+(2*c*d-b*e)*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[n,0] && NeQ[m+n+2*p+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(n_, 0)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let direct = g__.pow(&n_)
                * first.pow(&m_ + &n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &balance);
            let payload = rubi_expand_to_sum(
                &(&c__ * e__.pow(&n_) * &balance * second.pow(&n_)
                    - &c__ * g__.pow(&n_) * &balance * first.pow(&n_)
                    + &e__
                        * g__.pow(&n_)
                        * (&m_ + &p_ + &n_)
                        * first.pow(&n_ - Atom::num(2))
                        * (&b__ * &d__ - Atom::num(2) * &a__ * &e__
                            + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)),
                x_,
            );
            let recursive_integrand = first.pow(&m_) * quadratic.pow(&p_) * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&c__ * e__.pow(&n_) * balance), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1263,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[(f+g*x)^n,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(f+g*x)^n,a+b*x+c*x^2,x],x,1]},
          (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(R*b-2*a*S+(2*c*R-b*S)*x)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)*Q+S*(2*a*e*m+b*d*(2*p+3))-R*(b*e*m+2*c*d*(2*p+3))-e*(2*c*R-b*S)*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && GtQ[m,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let n_i = integer_i64(&n_).rubi_rhs();
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let (capital_q, remainder) =
                polynomial_quotient_remainder(&second.pow(n_i), &quadratic, x_).rubi_rhs();
            let capital_r = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let capital_s = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = (&p_ + Atom::num(1)) * &discriminant;
            let linear_remainder = Atom::num(2) * &c__ * &capital_r - &b__ * &capital_s;
            let direct = first.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * (&capital_r * &b__ - Atom::num(2) * &a__ * &capital_s
                    + &linear_remainder * x_)
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&denominator * &first * capital_q
                    + &capital_s
                        * (Atom::num(2) * &a__ * &e__ * &m_
                            + &b__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3)))
                    - &capital_r
                        * (&b__ * &e__ * &m_
                            + Atom::num(2)
                                * &c__
                                * &d__
                                * (Atom::num(2) * &p_ + Atom::num(3)))
                    - &e__
                        * &linear_remainder
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive_integrand = first.pow(&m_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1264,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(d+e*x)^m*(f+g*x)^n,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[(d+e*x)^m*(f+g*x)^n,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(d+e*x)^m*(f+g*x)^n,a+b*x+c*x^2,x],x,1]},
          (b*R-2*a*S+(2*c*R-b*S)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)^(-m)*Q-(2*p+3)*(2*c*R-b*S)*(d+e*x)^(-m),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[n,1] && LtQ[p,-1] && ILtQ[m,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &raised_p * &discriminant;

            let first_denominator = first_affine.pow(-m_i);
            let (capital_q, capital_r) = polynomial_quotient_remainder_rational_dividend(
                &second_affine.pow(n_i),
                &first_denominator,
                &quadratic,
                x_,
            ).rubi_rhs();
            let capital_r_constant = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let capital_r_linear = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let linear_remainder = Atom::num(2) * &c__ * &capital_r_constant
                - &b__ * &capital_r_linear;
            let direct = (&b__ * &capital_r_constant
                    - Atom::num(2) * &a__ * &capital_r_linear
                    + &linear_remainder * x_)
                    * quadratic.pow(&raised_p)
                    / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&denominator * &first_denominator * capital_q
                    - (Atom::num(2) * &p_ + Atom::num(3))
                        * linear_remainder
                        * &first_denominator),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first_affine.pow(&m_)
                    * quadratic.pow(raised_p)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1265,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[(f+g*x)^n,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(f+g*x)^n,a+b*x+c*x^2,x],x,1]},
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)*(R*(b*c*d-b^2*e+2*a*c*e)-a*S*(2*c*d-b*e)+c*(R*(2*c*d-b*e)-S*(b*d-2*a*e))*x)/
            ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) +
          1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
           ExpandToSum[(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)*Q+
              R*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
              S*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
              c*e*(S*(b*d-2*a*e)-R*(2*c*d-b*e))*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && IGtQ[n,1] && LtQ[p,-1] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && igtq!(n_, 1)
                && ltq!(p_, -1)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let n_i = integer_i64(&n_).rubi_rhs();
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let (capital_q, remainder) =
                polynomial_quotient_remainder(&second.pow(n_i), &quadratic, x_).rubi_rhs();
            let capital_r = polynomial_coefficient(&remainder, x_, 0).rubi_rhs();
            let capital_s = polynomial_coefficient(&remainder, x_, 1).rubi_rhs();
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&p_ + Atom::num(1)) * &discriminant * &invariant;
            let two_c_d_minus_b_e = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let b_d_minus_two_a_e = &b__ * &d__ - Atom::num(2) * &a__ * &e__;
            let direct_numerator = &capital_r
                * (&b__ * &c__ * &d__ - b__.pow(2) * &e__
                    + Atom::num(2) * &a__ * &c__ * &e__)
                - &a__ * &capital_s * &two_c_d_minus_b_e
                + &c__
                    * (&capital_r * &two_c_d_minus_b_e
                        - &capital_s * &b_d_minus_two_a_e)
                    * x_;
            let direct = first.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                * direct_numerator
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&denominator * capital_q
                    + &capital_r
                        * (&b__
                            * &c__
                            * &d__
                            * &e__
                            * (Atom::num(2) * &p_ - &m_ + Atom::num(2))
                            + b__.pow(2)
                                * e__.pow(2)
                                * (&p_ + &m_ + Atom::num(2))
                            - Atom::num(2)
                                * c__.pow(2)
                                * d__.pow(2)
                                * (Atom::num(2) * &p_ + Atom::num(3))
                            - Atom::num(2)
                                * &a__
                                * &c__
                                * e__.pow(2)
                                * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                    - &capital_s
                        * (&a__
                            * &e__
                            * (&b__ * &e__ - Atom::num(2) * &c__ * &d__ * &m_
                                + &b__ * &e__ * &m_)
                            - &b__
                                * &d__
                                * (Atom::num(3) * &c__ * &d__ - &b__ * &e__
                                    + Atom::num(2) * &c__ * &d__ * &p_
                                    - &b__ * &e__ * &p_))
                    + &c__
                        * &e__
                        * (&capital_s * &b_d_minus_two_a_e
                            - &capital_r * &two_c_d_minus_b_e)
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                        * x_),
                x_,
            );
            let recursive_integrand = first.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1266,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,d+e*x,x], R=PolynomialRemainder[(f+g*x)^n,d+e*x,x]},
          (e*R*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1))/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
             ExpandToSum[(m+1)*(c*d^2-b*d*e+a*e^2)*Q+c*d*R*(m+1)-b*e*R*(m+p+2)-c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && IGtQ[n,1] && ILtQ[m,-1] && NeQ[c*d^2-b*d*e+a*e^2,0] && (NeQ[m+n,0] || EqQ[p,-1/2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && igtq!(n_, 1)
                && iltq!(m_, -1)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (neq!(&m_ + &n_, 0)
                    || eqq!(p_, -Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let n_i = integer_i64(&n_).rubi_rhs();
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let (capital_q, capital_r) = polynomial_quotient_remainder_linear(
                &second.pow(n_i),
                &d__,
                &e__,
                x_,
            ).rubi_rhs();
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = &e__
                * &capital_r
                * first.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&denominator * &capital_q
                    + &c__ * &d__ * &capital_r * (&m_ + Atom::num(1))
                    - &b__ * &e__ * &capital_r * (&m_ + &p_ + Atom::num(2))
                    - &c__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive_integrand = first.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_)
                * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1267,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-
            g^n*(d+e*x)^(n-2)*(b*d*e*(p+1)+a*e^2*(m+n-1)-c*d^2*(m+n+2*p+1)-e*(2*c*d-b*e)*(m+n+p)*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && IGtQ[n,1] && IntegerQ[m] && NeQ[m+n+2*p+1,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && igtq!(n_, 1)
                && integerq!(m_)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let direct = g__.pow(&n_)
                * first.pow(&m_ + &n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &balance);
            let payload = rubi_expand_to_sum(
                &(&c__ * e__.pow(&n_) * &balance * second.pow(&n_)
                    - &c__ * g__.pow(&n_) * &balance * first.pow(&n_)
                    - g__.pow(&n_)
                        * first.pow(&n_ - Atom::num(2))
                        * (&b__ * &d__ * &e__ * (&p_ + Atom::num(1))
                            + &a__ * e__.pow(2) * (&m_ + &n_ - Atom::num(1))
                            - &c__ * d__.pow(2) * &balance
                            - &e__
                                * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                                * (&m_ + &n_ + &p_)
                                * x_)),
                x_,
            );
            let recursive_integrand = first.pow(&m_) * quadratic.pow(&p_) * payload;
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&c__ * e__.pow(&n_) * balance), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1268,
        source: "Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p]) \\[Star] Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, e__, f__, g__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let reduced_linear = &a__ / &d__ + &c__ * x_ / &e__;
            let fractional_part = rubi_frac_part(&p_);
            let prefactor = quadratic.pow(&fractional_part)
                / (first.pow(&fractional_part) * reduced_linear.pow(&fractional_part));
            let recursive_integrand = first.pow(&m_ + &p_)
                * second.pow(&n_)
                * reduced_linear.pow(&p_);
            rubi_simp(&(&prefactor * &rubi_rhs_int(&recursive_integrand, x_)), x_)
        },
    ));
}

fn push_rules_rule_1269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1269,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          g/e \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] + (e*f-d*g)/e \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && Not[IGtQ[m,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_) && !igtq!(m_, 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first_integrand = first.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_);
            let second_integrand = first.pow(&m_) * quadratic.pow(&p_);
            rubi_star(&g__ / &e__, rubi_rhs_int(&first_integrand, x_)) + rubi_star((&e__ * &f__ - &d__ * &g__) / &e__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 1270,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g)) \\[Star] Int[(a+b*x+c*x^2)^(p-1)/(d+e*x),x] -
          1/(e*(e*f-d*g)) \\[Star] Int[Simp[c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x,x]*(a+b*x+c*x^2)^(p-1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && FractionQ[p] && GtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
            / ((d__ + e__ * x_) * (f__ + g__ * x_)),
        with: [a__, b__, c__, d__, e__, f__, g__, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && fractionq!(p_)
                && gtq!(p_, 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = &e__ * (&e__ * &f__ - &d__ * &g__);
            let reduced_quadratic = quadratic.pow(&p_ - Atom::num(1));
            let first_integrand = &reduced_quadratic / first;
            let second_integrand = rubi_simp(
                &(&c__ * &d__ * &f__ - &b__ * &e__ * &f__ + &a__ * &e__ * &g__
                    - &c__ * (&e__ * &f__ - &d__ * &g__) * x_),
                x_,
            ) * reduced_quadratic
                / second;
            rubi_star(&invariant / &denominator, rubi_rhs_int(&first_integrand, x_)) - rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1271,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(e*(m+1)) -
          1/(2*e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*Simp[b*f+a*g+2*(c*f+b*g)*x+3*c*g*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let payload = rubi_simp(
                &(&b__ * &f__
                    + &a__ * &g__
                    + Atom::num(2) * (&c__ * &f__ + &b__ * &g__) * x_
                    + Atom::num(3) * &c__ * &g__ * x_.pow(2)),
                x_,
            );
            let denominator = &e__ * &m_plus_one;
            let direct = linear.pow(&m_plus_one) * binomial.sqrt() * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(m_plus_one) * payload / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1272,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(e*(2*m+5)) -
          1/(e*(2*m+5)) \\[Star] Int[(d+e*x)^m/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[b*d*f-3*a*e*f+a*d*g+2*(c*d*f-b*e*f+b*d*g-a*e*g)*x-(c*e*f-3*c*d*g+b*e*g)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && IntegerQ[2*m] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && integerq!(Atom::num(2) * &m_)
                && !ltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&b__ * &d__ * &f__ - Atom::num(3) * &a__ * &e__ * &f__
                    + &a__ * &d__ * &g__
                    + Atom::num(2)
                        * (&c__ * &d__ * &f__ - &b__ * &e__ * &f__
                            + &b__ * &d__ * &g__ - &a__ * &e__ * &g__)
                        * x_
                    - (&c__ * &e__ * &f__ - Atom::num(3) * &c__ * &d__ * &g__
                        + &b__ * &e__ * &g__)
                        * x_.pow(2)),
                x_,
            );
            let denominator = &e__ * (Atom::num(2) * &m_ + Atom::num(5));
            let direct = Atom::num(2)
                * linear.pow(&m_ + Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_) * payload / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1273,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[a_.+b_.*x_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
          2*(d+e*x)^m*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(g*(2*m+3)) -
          1/(g*(2*m+3)) \\[Star] Int[(d+e*x)^(m-1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[b*d*f+2*a*(e*f*m-d*g*(m+1))+(2*c*d*f-2*a*e*g+b*(e*f-d*g)*(2*m+1))*x-(b*e*g+2*c*(d*g*m-e*f*(m+1)))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&b__ * &d__ * &f__
                    + Atom::num(2)
                        * &a__
                        * (&e__ * &f__ * &m_ - &d__ * &g__ * (&m_ + Atom::num(1)))
                    + (Atom::num(2) * &c__ * &d__ * &f__
                        - Atom::num(2) * &a__ * &e__ * &g__
                        + &b__
                            * (&e__ * &f__ - &d__ * &g__)
                            * (Atom::num(2) * &m_ + Atom::num(1)))
                        * x_
                    - (&b__ * &e__ * &g__
                        + Atom::num(2)
                            * &c__
                            * (&d__ * &g__ * &m_
                                - &e__ * &f__ * (&m_ + Atom::num(1))))
                        * x_.pow(2)),
                x_,
            );
            let denominator = &g__ * (Atom::num(2) * &m_ + Atom::num(3));
            let direct = Atom::num(2)
                * linear.pow(&m_)
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(1)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1274,
        source: "Int[Sqrt[a_.+b_.*x_+c_.*x_^2]/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)/e^2 \\[Star] Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] -
          1/e^2 \\[Star] Int[(c*d-b*e-c*e*x)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()
            / ((d__ + e__ * x_) * (f__ + g__ * x_).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = e__.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&linear * binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &((&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_)
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&invariant / &denominator, first)
                    - rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_1275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1275,
        source: "Int[(d_.+e_.*x_)^m_.*Sqrt[a_.+b_.*x_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
          (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(e*f-d*g)) -
          1/(2*(m+1)*(e*f-d*g)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[b*f+a*g*(2*m+3)+2*(c*f+b*g*(m+2))*x+c*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let m_plus_one = &m_ + Atom::num(1);
            let payload = rubi_simp(
                &(&b__ * &f__
                    + &a__ * &g__ * (Atom::num(2) * &m_ + Atom::num(3))
                    + Atom::num(2)
                        * (&c__ * &f__ + &b__ * &g__ * (&m_ + Atom::num(2)))
                        * x_
                    + &c__ * &g__ * (Atom::num(2) * &m_ + Atom::num(5))
                        * x_.pow(2)),
                x_,
            );
            let denominator = &m_plus_one * (&e__ * &f__ - &d__ * &g__);
            let direct = linear.pow(&m_plus_one) * binomial.sqrt() * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(m_plus_one) * payload / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1276,
        source: "Int[Sqrt[d_.+e_.*x_]/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[2]*Sqrt[2*c*f-g*(b+q)]*Sqrt[b-q+2*c*x]*(d+e*x)*
            Sqrt[(e*f-d*g)*(b+q+2*c*x)/((2*c*f-g*(b+q))*(d+e*x))]*
            Sqrt[(e*f-d*g)*(2*a+(b+q)*x)/((b*f+q*f-2*a*g)*(d+e*x))]/
           (g*Sqrt[2*c*d-e*(b+q)]*Sqrt[2*a*c/(b+q)+c*x]*Sqrt[a+b*x+c*x^2])*
            EllipticPi[e*(2*c*f-g*(b+q))/(g*(2*c*d-e*(b+q))),
              ArcSin[Sqrt[2*c*d-e*(b+q)]*Sqrt[f+g*x]/(Sqrt[2*c*f-g*(b+q)]*Sqrt[d+e*x])],
              (b*d+q*d-2*a*e)*(2*c*f-g*(b+q))/((b*f+q*f-2*a*g)*(2*c*d-e*(b+q)))]] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ + e__ * x_).sqrt()
            / ((f__ + g__ * x_).sqrt()
                * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let ef_minus_dg = &e__ * &f__ - &d__ * &g__;
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let two_cf_minus_g_bq = Atom::num(2) * &c__ * &f__ - &g__ * &b_plus_q;
            let two_cd_minus_e_bq = Atom::num(2) * &c__ * &d__ - &e__ * &b_plus_q;
            let bq_f_minus_two_ag = &b_plus_q * &f__ - Atom::num(2) * &a__ * &g__;
            rubi_simp(&(Atom::num(2).sqrt()
                    * two_cf_minus_g_bq.sqrt()
                    * (&b__ - &q + Atom::num(2) * &c__ * x_).sqrt()
                    * &linear
                    * (&ef_minus_dg * (&b_plus_q + Atom::num(2) * &c__ * x_)
                        / (&two_cf_minus_g_bq * &linear))
                        .sqrt()
                    * (&ef_minus_dg * (Atom::num(2) * &a__ + &b_plus_q * x_)
                        / (&bq_f_minus_two_ag * &linear))
                        .sqrt()
                    * rubi_elliptic_pi(
                        &e__ * &two_cf_minus_g_bq / (&g__ * &two_cd_minus_e_bq),
                        (two_cd_minus_e_bq.sqrt() * binomial.sqrt()
                            / (two_cf_minus_g_bq.sqrt() * linear.sqrt()))
                        .asin(),
                        (&b_plus_q * &d__ - Atom::num(2) * &a__ * &e__)
                            * &two_cf_minus_g_bq
                            / (&bq_f_minus_two_ag * &two_cd_minus_e_bq),
                    )
                    / (&g__
                        * two_cd_minus_e_bq.sqrt()
                        * (Atom::num(2) * &a__ * &c__ / &b_plus_q + &c__ * x_)
                            .sqrt()
                        * quadratic.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_1277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1277,
        source: "Int[(d_.+e_.*x_)^(3/2)/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          e/g \\[Star] Int[Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[a+b*x+c*x^2],x] -
          (e*f-d*g)/g \\[Star] Int[Sqrt[d+e*x]/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow((3, 2))
            / ((f__ + g__ * x_).sqrt()
                * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(linear.sqrt() * binomial.sqrt() / quadratic.sqrt()),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.sqrt() / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&e__ / &g__, first)
                    - rubi_star((&e__ * &f__ - &d__ * &g__) / &g__, second)
        },
    ));
}

fn push_rules_rule_1278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1278,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          2*e^2*(d+e*x)^(m-2)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(c*g*(2*m-1)) -
          1/(c*g*(2*m-1)) \\[Star] Int[(d+e*x)^(m-3)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[b*d*e^2*f+a*e^2*(d*g+2*e*f*(m-2))-c*d^3*g*(2*m-1)+
              e*(e*(2*b*d*g+e*(b*f+a*g)*(2*m-3))+c*d*(2*e*f-3*d*g*(2*m-1)))*x+
              2*e^2*(c*e*f-3*c*d*g+b*e*g)*(m-1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && GeQ[m,2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && geq!(m_, 2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&b__ * &d__ * e__.pow(2) * &f__
                    + &a__
                        * e__.pow(2)
                        * (&d__ * &g__
                            + Atom::num(2) * &e__ * &f__ * (&m_ - Atom::num(2)))
                    - &c__ * d__.pow(3) * &g__ * (Atom::num(2) * &m_ - Atom::num(1))
                    + &e__
                        * (&e__
                            * (Atom::num(2) * &b__ * &d__ * &g__
                                + &e__
                                    * (&b__ * &f__ + &a__ * &g__)
                                    * (Atom::num(2) * &m_ - Atom::num(3)))
                            + &c__
                                * &d__
                                * (Atom::num(2) * &e__ * &f__
                                    - Atom::num(3)
                                        * &d__
                                        * &g__
                                        * (Atom::num(2) * &m_ - Atom::num(1))))
                        * x_
                    + Atom::num(2)
                        * e__.pow(2)
                        * (&c__ * &e__ * &f__ - Atom::num(3) * &c__ * &d__ * &g__
                            + &b__ * &e__ * &g__)
                        * (&m_ - Atom::num(1))
                        * x_.pow(2)),
                x_,
            );
            let denominator = &c__ * &g__ * (Atom::num(2) * &m_ - Atom::num(1));
            let direct = Atom::num(2)
                * e__.pow(2)
                * linear.pow(&m_ - Atom::num(2))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(3)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1279,
        source: "Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[b-q+2*c*x]*Sqrt[b+q+2*c*x]/Sqrt[a+b*x+c*x^2] \\[Star] Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[b-q+2*c*x]*Sqrt[b+q+2*c*x]),x]] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1)
            / ((d__ + e__ * x_)
                * (f__ + g__ * x_).sqrt()
                * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first = &b__ - &q + Atom::num(2) * &c__ * x_;
            let second = &b__ + &q + Atom::num(2) * &c__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&d__ + &e__ * x_)
                        * (&f__ + &g__ * x_).sqrt()
                        * first.sqrt()
                        * second.sqrt())),
                x_,
            );
            rubi_star(first.sqrt() * second.sqrt() / quadratic.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_1280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1280,
        source: "Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          -2*(d+e*x)*Sqrt[(e*f-d*g)^2*(a+b*x+c*x^2)/((c*f^2-b*f*g+a*g^2)*(d+e*x)^2)]/((e*f-d*g)*Sqrt[a+b*x+c*x^2]) \\[Star]
          Subst[
            Int[1/Sqrt[1-(2*c*d*f-b*e*f-b*d*g+2*a*e*g)*x^2/(c*f^2-b*f*g+a*g^2)+(c*d^2-b*d*e+a*e^2)*x^4/(c*f^2-b*f*g+a*g^2)],x],
            x,
            Sqrt[f+g*x]/Sqrt[d+e*x]] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1)
            / ((d__ + e__ * x_).sqrt()
                * (f__ + g__ * x_).sqrt()
                * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_minus_dg = &e__ * &f__ - &d__ * &g__;
            let invariant_f = &c__ * f__.pow(2) - &b__ * &f__ * &g__ + &a__ * g__.pow(2);
            let invariant_d = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let prefactor = -Atom::num(2)
                * &linear
                * (ef_minus_dg.pow(2) * &quadratic / (&invariant_f * linear.pow(2)))
                    .sqrt()
                / (&ef_minus_dg * quadratic.sqrt());
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub = Atom::var(sub_symbol);
            let transformed = rubi_rhs_int(
                &(Atom::num(1)
                    / (Atom::num(1)
                        - (Atom::num(2) * &c__ * &d__ * &f__
                            - &b__ * &e__ * &f__ - &b__ * &d__ * &g__
                            + Atom::num(2) * &a__ * &e__ * &g__)
                            * sub.pow(2)
                            / &invariant_f
                        + &invariant_d * sub.pow(4) / &invariant_f)
                        .sqrt()),
                sub_symbol,
            );
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                binomial.sqrt() / linear.sqrt(),
            );
            rubi_star(prefactor, substituted)
        },
    ));
}

fn push_rules_rule_1281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1281,
        source: "Int[1/((d_.+e_.*x_)^(3/2)*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          -g/(e*f-d*g) \\[Star] Int[1/(Sqrt[d+e*x]*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] +
          e/(e*f-d*g) \\[Star] Int[Sqrt[f+g*x]/((d+e*x)^(3/2)*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((d__ + e__ * x_).pow((3, 2))
                * (f__ + g__ * x_).sqrt()
                * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = &e__ * &f__ - &d__ * &g__;
            let first = rubi_rhs_int(
                &(Atom::num(1) / (linear.sqrt() * binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &(binomial.sqrt() / (linear.pow((3, 2)) * quadratic.sqrt())),
                x_,
            );
            rubi_star(-&g__ / &denominator, first)
                    + rubi_star(&e__ / denominator, second)
        },
    ));
}

fn push_rules_rule_1282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1282,
        source: "Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          e^2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(e*f-d*g)*(c*d^2-b*d*e+a*e^2)) +
          1/(2*(m+1)*(e*f-d*g)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[2*d*(c*e*f-c*d*g+b*e*g)*(m+1)-e^2*(b*f+a*g)*(2*m+3)+2*e*(c*d*g*(m+1)-e*(c*f+b*g)*(m+2))*x-c*e^2*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && LeQ[m,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && leq!(m_, -2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_minus_dg = &e__ * &f__ - &d__ * &g__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let payload = rubi_simp(
                &(Atom::num(2)
                    * &d__
                    * (&c__ * &e__ * &f__ - &c__ * &d__ * &g__ + &b__ * &e__ * &g__)
                    * (&m_ + Atom::num(1))
                    - e__.pow(2)
                        * (&b__ * &f__ + &a__ * &g__)
                        * (Atom::num(2) * &m_ + Atom::num(3))
                    + Atom::num(2)
                        * &e__
                        * (&c__ * &d__ * &g__ * (&m_ + Atom::num(1))
                            - &e__
                                * (&c__ * &f__ + &b__ * &g__)
                                * (&m_ + Atom::num(2)))
                        * x_
                    - &c__
                        * e__.pow(2)
                        * &g__
                        * (Atom::num(2) * &m_ + Atom::num(5))
                        * x_.pow(2)),
                x_,
            );
            let denominator = (&m_ + Atom::num(1)) * &ef_minus_dg * &invariant;
            let direct = e__.pow(2)
                * linear.pow(&m_ + Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ + Atom::num(1)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1283,
        source: "Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          2*e*(d+e*x)^(m-1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(c*(2*m+1)) -
          1/(c*(2*m+1)) \\[Star] Int[(d+e*x)^(m-2)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[e*(b*d*f+a*(d*g+2*e*f*(m-1)))-c*d^2*f*(2*m+1)+
              (a*e^2*g*(2*m-1)-c*d*(4*e*f*m+d*g*(2*m+1))+b*e*(2*d*g+e*f*(2*m-1)))*x+
              e*(2*b*e*g*m-c*(e*f+d*g*(4*m-1)))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && GtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let payload = rubi_simp(
                &(&e__
                    * (&b__ * &d__ * &f__
                        + &a__
                            * (&d__ * &g__
                                + Atom::num(2)
                                    * &e__
                                    * &f__
                                    * (&m_ - Atom::num(1))))
                    - &c__ * d__.pow(2) * &f__ * (Atom::num(2) * &m_ + Atom::num(1))
                    + (&a__ * e__.pow(2) * &g__ * (Atom::num(2) * &m_ - Atom::num(1))
                        - &c__
                            * &d__
                            * (Atom::num(4) * &e__ * &f__ * &m_
                                + &d__ * &g__ * (Atom::num(2) * &m_ + Atom::num(1)))
                        + &b__
                            * &e__
                            * (Atom::num(2) * &d__ * &g__
                                + &e__ * &f__ * (Atom::num(2) * &m_ - Atom::num(1))))
                        * x_
                    + &e__
                        * (Atom::num(2) * &b__ * &e__ * &g__ * &m_
                            - &c__
                                * (&e__ * &f__
                                    + &d__ * &g__ * (Atom::num(4) * &m_ - Atom::num(1))))
                        * x_.pow(2)),
                x_,
            );
            let denominator = &c__ * (Atom::num(2) * &m_ + Atom::num(1));
            let direct = Atom::num(2)
                * &e__
                * linear.pow(&m_ - Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - Atom::num(2)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 1284,
        source: "Int[Sqrt[f_.+g_.*x_]/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          g/e \\[Star] Int[1/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] +
          (e*f-d*g)/e \\[Star] Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).sqrt()
            / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__], x_) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            let second = rubi_rhs_int(
                &(Atom::num(1) / (linear * binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_star(&g__ / &e__, first)
                    + rubi_star((&e__ * &f__ - &d__ * &g__) / &e__, second)
        },
    ));
}

fn push_rules_rule_1285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 1285,
        source: "Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
            Simp[2*c*d*f*(m+1)-e*(a*g+b*f*(2*m+3))-2*(b*e*g*(2+m)-c*(d*g*(m+1)-e*f*(m+2)))*x-c*e*g*(2*m+5)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[2*m] && LeQ[m,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(Atom::num(2) * &m_)
                && leq!(m_, -2)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let payload = rubi_simp(
                &(Atom::num(2) * &c__ * &d__ * &f__ * (&m_ + Atom::num(1))
                    - &e__
                        * (&a__ * &g__
                            + &b__ * &f__ * (Atom::num(2) * &m_ + Atom::num(3)))
                    - Atom::num(2)
                        * (&b__ * &e__ * &g__ * (&m_ + Atom::num(2))
                            - &c__
                                * (&d__ * &g__ * (&m_ + Atom::num(1))
                                    - &e__ * &f__ * (&m_ + Atom::num(2))))
                        * x_
                    - &c__
                        * &e__
                        * &g__
                        * (Atom::num(2) * &m_ + Atom::num(5))
                        * x_.pow(2)),
                x_,
            );
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = &e__
                * linear.pow(&m_ + Atom::num(1))
                * binomial.sqrt()
                * quadratic.sqrt()
                / &denominator;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ + Atom::num(1)) * payload
                    / (binomial.sqrt() * quadratic.sqrt())),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1286,
        source: "Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g)) \\[Star] Int[(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1)/(d+e*x),x] -
          1/(e*(e*f-d*g)) \\[Star] Int[(f+g*x)^n*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && GtQ[p,0] && LtQ[n,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && !integerq!(n_)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_minus_dg = &e__ * &f__ - &d__ * &g__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let factor = &c__ * &d__ * &f__ - &b__ * &e__ * &f__
                + &a__ * &e__ * &g__ - &c__ * &ef_minus_dg * x_;
            let first = rubi_rhs_int(
                &(binomial.pow(&n_ + Atom::num(1))
                    * quadratic.pow(&p_ - Atom::num(1))
                    / &linear),
                x_,
            );
            let second = rubi_rhs_int(
                &(binomial.pow(&n_) * factor * quadratic.pow(&p_ - Atom::num(1))),
                x_,
            );
            let denominator = &e__ * &ef_minus_dg;
            rubi_star(&invariant / &denominator, first)
                    - rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_1287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1287,
        source: "Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
          e*(e*f-d*g)/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1)/(d+e*x),x] +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f+g*x)^(n-1)*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g},x] &&
          Not[IntegerQ[n]] && Not[IntegerQ[p]] && LtQ[p,-1] && GtQ[n,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && !integerq!(n_)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let ef_minus_dg = &e__ * &f__ - &d__ * &g__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let factor = &c__ * &d__ * &f__ - &b__ * &e__ * &f__
                + &a__ * &e__ * &g__ - &c__ * &ef_minus_dg * x_;
            let first = rubi_rhs_int(
                &(binomial.pow(&n_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &linear),
                x_,
            );
            let second = rubi_rhs_int(
                &(binomial.pow(&n_ - Atom::num(1)) * factor * quadratic.pow(&p_)),
                x_,
            );
            rubi_star(&e__ * &ef_minus_dg / &invariant, first)
                    + rubi_star(Atom::num(1) / invariant, second)
        },
    ));
}

fn push_rules_rule_1288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 1288,
        source: "Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
          Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[n+1/2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: ["Algebraic expansion"],
        pattern: (f__ + g__ * x_).pow(n_)
            / ((d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && integerq!(&n_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let binomial = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let u = Atom::num(1) / (binomial.sqrt() * quadratic.sqrt());
            let v = binomial.pow(&n_ + Atom::num(1) / Atom::num(2))
                / (&d__ + &e__ * x_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1289,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && (IntegerQ[p] || ILtQ[m,0] && ILtQ[n,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && (integerq!(p_) || iltq!(m_, 0) && iltq!(n_, 0))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1290,
        source: "Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(f+g*x)^n,d+e*x,x], R=PolynomialRemainder[(f+g*x)^n,d+e*x,x]},
          (e*R*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1))/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
             ExpandToSum[(m+1)*(c*d^2-b*d*e+a*e^2)*Q+c*d*R*(m+1)-b*e*R*(m+p+2)-c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && IGtQ[n,1] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && igtq!(n_, 1)
                && ltq!(m_, -1)
        },
        rhs: {
            let n_i = integer_i64(&n_).rubi_rhs();
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let (capital_q, capital_r) = polynomial_quotient_remainder_linear(
                &second.pow(n_i),
                &d__,
                &e__,
                x_,
            ).rubi_rhs();
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            let direct = &e__
                * &capital_r
                * first.pow(&m_ + Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&denominator * &capital_q
                    + &c__ * &d__ * &capital_r * (&m_ + Atom::num(1))
                    - &b__ * &e__ * &capital_r * (&m_ + &p_ + Atom::num(2))
                    - &c__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1291,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          g^n*(d+e*x)^(m+n-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) +
          1/(c*e^n*(m+n+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-
            g^n*(d+e*x)^(n-2)*(b*d*e*(p+1)+a*e^2*(m+n-1)-c*d^2*(m+n+2*p+1)-e*(2*c*d-b*e)*(m+n+p)*x),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && IGtQ[n,1] && NeQ[m+n+2*p+1,0]",
        desc: "Algebraic expansion and special quadratic recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && igtq!(n_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let first = &d__ + &e__ * x_;
            let second = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = &m_ + &n_ + Atom::num(2) * &p_ + Atom::num(1);
            let direct = g__.pow(&n_)
                * first.pow(&m_ + &n_ - Atom::num(1))
                * quadratic.pow(&p_ + Atom::num(1))
                / (&c__ * e__.pow(&n_ - Atom::num(1)) * &balance);
            let payload = rubi_expand_to_sum(
                &(&c__ * e__.pow(&n_) * &balance * second.pow(&n_)
                    - &c__ * g__.pow(&n_) * &balance * first.pow(&n_)
                    - g__.pow(&n_)
                        * first.pow(&n_ - Atom::num(2))
                        * (&b__ * &d__ * &e__ * (&p_ + Atom::num(1))
                            + &a__ * e__.pow(2) * (&m_ + &n_ - Atom::num(1))
                            - &c__ * d__.pow(2) * &balance
                            - &e__
                                * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                                * (&m_ + &n_ + &p_)
                                * x_)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(&m_) * quadratic.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&c__ * e__.pow(&n_) * balance), recursive)
        },
    ));
}

fn push_rules_rule_1292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1292,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Unintegrable[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, n_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&d__ + &e__ * x_).pow(&m_)
                    * (&f__ + &g__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 1293,
        source: "Int[(d_.+e_.*u_)^m_.*(f_.+g_.*u_)^n_.*(a_+b_.*u_+c_.*u_^2)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x,u] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * u_).pow(m_)
            * (f__ + g__ * u_).pow(n_)
            * (a__ + b__ * u_ + c__ * u_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, u_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_, n_, p_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_],
        x_linear: [u_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * &sub_atom).pow(&m_)
                * (&f__ + &g__ * &sub_atom).pow(&n_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, sub, u_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (f__ + g__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt() / (f__ + g__ * x_).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).pow(n_) / (a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_).sqrt() / (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_) / (a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) / ((f__ + g__ * x_).sqrt() * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(n_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_) / (d__ + e__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(n_) * (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}
