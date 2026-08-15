use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1792(rules);
    push_rules_rule_1793(rules);
    push_rules_rule_1794(rules);
    push_rules_rule_1795(rules);
    push_rules_rule_1796(rules);
    push_rules_rule_1797(rules);
    push_rules_rule_1798(rules);
    push_rules_rule_1799(rules);
    push_rules_rule_1800(rules);
    push_rules_rule_1801(rules);
    push_rules_rule_1802(rules);
    push_rules_rule_1803(rules);
    push_rules_rule_1804(rules);
    push_rules_rule_1805(rules);
    push_rules_rule_1806(rules);
    push_rules_rule_1807(rules);
    push_rules_rule_1808(rules);
    push_rules_rule_1809(rules);
    push_rules_rule_1810(rules);
    push_rules_rule_1811(rules);
    push_rules_rule_1812(rules);
    push_rules_rule_1813(rules);
    push_rules_rule_1814(rules);
    push_rules_rule_1815(rules);
    push_rules_rule_1816(rules);
    push_rules_rule_1817(rules);
    push_rules_rule_1818(rules);
    push_rules_rule_1819(rules);
    push_rules_rule_1820(rules);
    push_rules_rule_1821(rules);
    push_rules_rule_1822(rules);
    push_rules_rule_1823(rules);
    push_rules_rule_1824(rules);
    push_rules_rule_1825(rules);
    push_rules_rule_1826(rules);
    push_rules_rule_1827(rules);
    push_rules_rule_1828(rules);
    push_rules_rule_1829(rules);
    push_rules_rule_1830(rules);
    push_rules_rule_1831(rules);
    push_rules_rule_1832(rules);
    push_rules_rule_1833(rules);
    push_rules_rule_1834(rules);
    push_rules_rule_1835(rules);
    push_rules_rule_1836(rules);
    push_rules_rule_1837(rules);
    push_rules_rule_1838(rules);
    push_rules_rule_1839(rules);
    push_rules_rule_1840(rules);
    push_rules_rule_1841(rules);
    push_rules_rule_1842(rules);
    push_rules_rule_1843(rules);
    push_rules_rule_1844(rules);
    push_rules_rule_1845(rules);
    push_rules_rule_1846(rules);
    push_rules_rule_1847(rules);
    push_rules_rule_1848(rules);
    push_rules_rule_1849(rules);
    push_rules_rule_1850(rules);
    push_rules_rule_1851(rules);
    push_rules_rule_1852(rules);
    push_rules_rule_1853(rules);
    push_rules_rule_1854(rules);
    push_rules_rule_1855(rules);
    push_rules_rule_1856(rules);
    push_rules_rule_1857(rules);
    push_rules_rule_1858(rules);
    push_rules_rule_1859(rules);
    push_rules_rule_1860(rules);
    push_rules_rule_1861(rules);
    push_rules_rule_1862(rules);
    push_rules_rule_1863(rules);
    push_rules_rule_1864(rules);
    push_rules_rule_1865(rules);
    push_rules_rule_1866(rules);
    push_rules_rule_1867(rules);
    push_rules_rule_1868(rules);
    push_rules_rule_1869(rules);
    push_rules_rule_1870(rules);
    push_rules_rule_1871(rules);
    push_rules_rule_1872(rules);
    push_rules_rule_1873(rules);
    push_rules_rule_1874(rules);
    push_rules_rule_1875(rules);
    push_rules_rule_1876(rules);
    push_rules_rule_1877(rules);
    push_rules_rule_1878(rules);
    push_rules_rule_1879(rules);
    push_rules_rule_1880(rules);
    push_rules_rule_1881(rules);
    push_rules_rule_1882(rules);
    push_rules_rule_1883(rules);
    push_rules_rule_1884(rules);
    push_rules_rule_1885(rules);
    push_rules_rule_1886(rules);
    push_rules_rule_1887(rules);
    push_rules_rule_1888(rules);
    push_rules_rule_1889(rules);
    push_rules_rule_1890(rules);
    push_rules_rule_1891(rules);
    push_rules_rule_1892(rules);
    push_rules_rule_1893(rules);
    push_rules_rule_1894(rules);
    push_rules_rule_1895(rules);
    push_rules_rule_1896(rules);
    push_rules_rule_1897(rules);
    push_rules_rule_1898(rules);
    push_rules_rule_1899(rules);
    push_rules_rule_1900(rules);
    push_rules_rule_1901(rules);
    push_rules_rule_1902(rules);
    push_rules_rule_1903(rules);
    push_rules_rule_1904(rules);
    push_rules_rule_1905(rules);
}

fn push_rules_rule_1792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1792,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^m/(n*e^((m+1)/n-1)) \\[Star] Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && (IntegerQ[m] || GtQ[f,0]) && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [f__, m_, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && (integerq!(m_) || gtq!(f__, 0))
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&e__ * &sub_atom).pow(&q_ + &k - 1) * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(f__.pow(&m_), rubi_subst(&transformed, sub, x_.pow(&n_)) / (&n_ * e__.pow(&k - 1)))
        },
    ));
}

fn push_rules_rule_1793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1793,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^m/(n*e^((m+1)/n-1)) \\[Star] Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && (IntegerQ[m] || GtQ[f,0]) && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [f__, m_, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && (integerq!(m_) || gtq!(f__, 0))
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&e__ * &sub_atom).pow(&q_ + &k - 1) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(f__.pow(&m_), rubi_subst(&transformed, sub, x_.pow(&n_)) / (&n_ * e__.pow(&k - 1)))
        },
    ));
}

fn push_rules_rule_1794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1794,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q]) \\[Star] Int[x^(m+n*q)*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && (IntegerQ[m] || GtQ[f,0]) && Not[IntegerQ[Simplify[(m+1)/n]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [f__, m_, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && (integerq!(m_) || gtq!(f__, 0))
                && !integerq!(&k)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = x_.pow(&m_ + &n_ * &q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(&m_) * e__.pow(rubi_int_part(&q_)) * (&e__ * x_.pow(&n_)).pow(&frac_q) / x_.pow(&n_ * frac_q), recursive)
        },
    ));
}

fn push_rules_rule_1795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1795,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q]) \\[Star] Int[x^(m+n*q)*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && (IntegerQ[m] || GtQ[f,0]) && Not[IntegerQ[Simplify[(m+1)/n]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [f__, m_, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && (integerq!(m_) || gtq!(f__, 0))
                && !integerq!(&k)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand =
                x_.pow(&m_ + &n_ * &q_) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(&m_) * e__.pow(rubi_int_part(&q_)) * (&e__ * x_.pow(&n_)).pow(&frac_q) / x_.pow(&n_ * frac_q), recursive)
        },
    ));
}

fn push_rules_rule_1796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1796,
        source: "Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [f__, m_, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(m_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1797,
        source: "Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2,2*n] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [f__, m_, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, c__, n2_, p_],
        when: {
            freeq!([a__, c__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(m_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1798,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[Simplify[m-n+1],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(rubi_simplify(&(&m_ - &n_ + 1)), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, sub, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1799,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[Simplify[m-n+1],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(rubi_simplify(&(&m_ - &n_ + 1)), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, sub, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1800,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2,2*n] && IntegersQ[p,q] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + &n_ * (Atom::num(2) * &p_ + &q_))
                * (&e__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&c__ + &b__ * x_.pow(-&n_) + &a__ * x_.pow(Atom::num(-2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1801,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
        FreeQ[{a,c,d,e,m,n},x] && EqQ[n2,2*n] && IntegersQ[p,q] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + &n_ * (Atom::num(2) * &p_ + &q_))
                * (&e__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&c__ + &a__ * x_.pow(Atom::num(-2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1802,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k - 1)
                * (&d__ + &e__ * &sub_atom).pow(&q_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_1803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1803,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow(&k - 1) * (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_1804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1804,
        source: "Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&k)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1805,
        source: "Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_, p_],
        when: {
            let k = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(&k)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1806,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) +
          1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) \\[Star] Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+b*x^n+c*x^(2*n))^p-
              (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && igtq!(m_, 0)
        },
        rhs: {
            let mod_mn = rubi_mod(&m_, &n_).rubi_rhs();
            let quotient = (&m_ - &mod_mn) / &n_;
            let q1 = &q_ + 1;
            let e_power = Atom::num(2) * &p_ + &quotient;
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let neg_d_power = (-&d__).pow(&quotient - 1);
            let denominator = &n_ * e__.pow(&e_power) * &q1;
            let direct = &neg_d_power
                * discriminant.pow(&p_)
                * x_.pow(&mod_mn + 1)
                * binomial.pow(&q1)
                / &denominator;
            let together_argument = (Atom::num(1) / &binomial)
                * (&n_
                    * e__.pow(&e_power)
                    * &q1
                    * x_.pow(&m_ - &mod_mn)
                    * trinomial.pow(&p_)
                    - neg_d_power * discriminant.pow(&p_)
                        * (&d__ * (&mod_mn + 1)
                            + &e__ * (&mod_mn + &n_ * &q1 + 1) * x_.pow(&n_)));
            let expand_to_sum = rubi_expand_to_sum(&rubi_together(&together_argument), x_);
            let recursive_integrand = x_.pow(&mod_mn) * binomial.pow(&q1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1807,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) +
          1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) \\[Star] Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+c*x^(2*n))^p-
              (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
        FreeQ[{a,c,d,e},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && igtq!(m_, 0)
        },
        rhs: {
            let mod_mn = rubi_mod(&m_, &n_).rubi_rhs();
            let quotient = (&m_ - &mod_mn) / &n_;
            let q1 = &q_ + 1;
            let e_power = Atom::num(2) * &p_ + &quotient;
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let neg_d_power = (-&d__).pow(&quotient - 1);
            let denominator = &n_ * e__.pow(&e_power) * &q1;
            let direct = &neg_d_power
                * discriminant.pow(&p_)
                * x_.pow(&mod_mn + 1)
                * binomial.pow(&q1)
                / &denominator;
            let together_argument = (Atom::num(1) / &binomial)
                * (&n_
                    * e__.pow(&e_power)
                    * &q1
                    * x_.pow(&m_ - &mod_mn)
                    * trinomial.pow(&p_)
                    - neg_d_power * discriminant.pow(&p_)
                        * (&d__ * (&mod_mn + 1)
                            + &e__ * (&mod_mn + &n_ * &q1 + 1) * x_.pow(&n_)));
            let expand_to_sum = rubi_expand_to_sum(&rubi_together(&together_argument), x_);
            let recursive_integrand = x_.pow(&mod_mn) * binomial.pow(&q1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1808,
        source: "Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) +
          (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1)) \\[Star] Int[x^m*(d+e*x^n)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+b*x^n+c*x^(2*n))^p -
          (e^(-(m-Mod[m,n])/n)*(c*d^2-b*d*e+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[q,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let mod_mn = rubi_mod(&m_, &n_).rubi_rhs();
            let quotient = (&m_ - &mod_mn) / &n_;
            let q1 = &q_ + 1;
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let neg_d_power = (-&d__).pow(&quotient - 1);
            let direct_denominator = &n_ * e__.pow(Atom::num(2) * &p_ + &quotient) * &q1;
            let direct = &neg_d_power
                * discriminant.pow(&p_)
                * x_.pow(&mod_mn + 1)
                * binomial.pow(&q1)
                / &direct_denominator;
            let together_argument = (Atom::num(1) / &binomial)
                * (&n_ * (-&d__).pow(-&quotient + 1) * e__.pow(Atom::num(2) * &p_) * &q1 * trinomial.pow(&p_)
                    - e__.pow(-&quotient) * discriminant.pow(&p_) * x_.pow(-(&m_ - &mod_mn))
                        * (&d__ * (&mod_mn + 1)
                            + &e__ * (&mod_mn + &n_ * &q1 + 1) * x_.pow(&n_)));
            let expand_to_sum = rubi_expand_to_sum(&rubi_together(&together_argument), x_);
            let recursive_integrand = x_.pow(&m_) * binomial.pow(&q1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(neg_d_power, recursive
                        / (&n_ * e__.pow(Atom::num(2) * &p_) * &q1))
        },
    ));
}

fn push_rules_rule_1809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1809,
        source: "Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) +
          (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1)) \\[Star] Int[x^m*(d+e*x^n)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+c*x^(2*n))^p -
          (e^(-(m-Mod[m,n])/n)*(c*d^2+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
        FreeQ[{a,c,d,e},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[p,0] && IntegersQ[m,q] && ILtQ[q,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && integersq!([m_, q_])
                && iltq!(q_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let mod_mn = rubi_mod(&m_, &n_).rubi_rhs();
            let quotient = (&m_ - &mod_mn) / &n_;
            let q1 = &q_ + 1;
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let neg_d_power = (-&d__).pow(&quotient - 1);
            let direct_denominator = &n_ * e__.pow(Atom::num(2) * &p_ + &quotient) * &q1;
            let direct = &neg_d_power
                * discriminant.pow(&p_)
                * x_.pow(&mod_mn + 1)
                * binomial.pow(&q1)
                / &direct_denominator;
            let together_argument = (Atom::num(1) / &binomial)
                * (&n_ * (-&d__).pow(-&quotient + 1) * e__.pow(Atom::num(2) * &p_) * &q1 * trinomial.pow(&p_)
                    - e__.pow(-&quotient) * discriminant.pow(&p_) * x_.pow(-(&m_ - &mod_mn))
                        * (&d__ * (&mod_mn + 1)
                            + &e__ * (&mod_mn + &n_ * &q1 + 1) * x_.pow(&n_)));
            let expand_to_sum = rubi_expand_to_sum(&rubi_together(&together_argument), x_);
            let recursive_integrand = x_.pow(&m_) * binomial.pow(&q1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(neg_d_power, recursive
                        / (&n_ * e__.pow(Atom::num(2) * &p_) * &q1))
        },
    ));
}

fn push_rules_rule_1810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1810,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) +
          1/(e*(m+2*n*p+n*q+1)) \\[Star] Int[(f*x)^m*(d+e*x^n)^q*
            ExpandToSum[e*(m+2*n*p+n*q+1)*((a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && GtQ[2*n*p,n-1] &&
          Not[IntegerQ[q]] && NeQ[m+2*n*p+n*q+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_, p_],
        when: {
            let balance = &m_ + Atom::num(2) * &n_ * &p_ + &n_ * &q_ + 1;
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && gtq!(Atom::num(2) * &n_ * &p_, &n_ - 1)
                && !integerq!(q_)
                && neq!(balance, 0)
        },
        rhs: {
            let balance = &m_ + Atom::num(2) * &n_ * &p_ + &n_ * &q_ + 1;
            let direct_power = &m_ + Atom::num(2) * &n_ * &p_ - &n_ + 1;
            let c_p = c__.pow(&p_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = &c_p
                * (&f__ * x_).pow(&direct_power)
                * binomial.pow(&q_ + 1)
                / (&e__ * f__.pow(Atom::num(2) * &n_ * &p_ - &n_ + 1) * &balance);
            let expand_to_sum_payload = &e__
                * &balance
                * (trinomial.pow(&p_) - &c_p * x_.pow(Atom::num(2) * &n_ * &p_))
                - &d__ * c_p * &direct_power * x_.pow(Atom::num(2) * &n_ * &p_ - &n_);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand =
                (&f__ * x_).pow(&m_) * binomial.pow(&q_) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&e__ * balance), recursive)
        },
    ));
}

fn push_rules_rule_1811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1811,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) +
          1/(e*(m+2*n*p+n*q+1)) \\[Star] Int[(f*x)^m*(d+e*x^n)^q*
            ExpandToSum[e*(m+2*n*p+n*q+1)*((a+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[p,0] && GtQ[2*n*p,n-1] &&
          Not[IntegerQ[q]] && NeQ[m+2*n*p+n*q+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_, p_],
        when: {
            let balance = &m_ + Atom::num(2) * &n_ * &p_ + &n_ * &q_ + 1;
            freeq!([a__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && gtq!(Atom::num(2) * &n_ * &p_, &n_ - 1)
                && !integerq!(q_)
                && neq!(balance, 0)
        },
        rhs: {
            let balance = &m_ + Atom::num(2) * &n_ * &p_ + &n_ * &q_ + 1;
            let direct_power = &m_ + Atom::num(2) * &n_ * &p_ - &n_ + 1;
            let c_p = c__.pow(&p_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = &c_p
                * (&f__ * x_).pow(&direct_power)
                * binomial.pow(&q_ + 1)
                / (&e__ * f__.pow(Atom::num(2) * &n_ * &p_ - &n_ + 1) * &balance);
            let expand_to_sum_payload = &e__
                * &balance
                * (trinomial.pow(&p_) - &c_p * x_.pow(Atom::num(2) * &n_ * &p_))
                - &d__ * c_p * &direct_power * x_.pow(Atom::num(2) * &n_ * &p_ - &n_);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand =
                (&f__ * x_).pow(&m_) * binomial.pow(&q_) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&e__ * balance), recursive)
        },
    ));
}

fn push_rules_rule_1812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1812,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1813,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1814,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + Atom::num(1)), &n_).is_some_and(|k| k != 1)
        },
        rhs: {
            let k = Atom::num(rubi_gcd(&(&m_ + Atom::num(1)), &n_).rubi_rhs());
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &k - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&n_ / &k)).pow(&q_)
                * (&a__
                    + &b__ * sub_atom.pow(&n_ / &k)
                    + &c__ * sub_atom.pow(Atom::num(2) * (&n_ / &k)))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_1815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1815,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+c*x^(2*n/k))^p,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,c,d,e,p,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + Atom::num(1)), &n_).is_some_and(|k| k != 1)
        },
        rhs: {
            let k = Atom::num(rubi_gcd(&(&m_ + Atom::num(1)), &n_).rubi_rhs());
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &k - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&n_ / &k)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * (&n_ / &k))).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_1816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1816,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/f \\[Star] Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f^n)^q*(a+b*x^(k*n)/f^n+c*x^(2*k*n)/f^(2*n))^p,x],x,(f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&k * &n_) / f__.pow(&n_)).pow(&q_)
                * (&a__
                    + &b__ * sub_atom.pow(&k * &n_) / f__.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &k * &n_) / f__.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&f__ * x_).pow(Atom::num(1) / Atom::num(k_i));

            rubi_star(k, rubi_subst(&transformed, sub, replacement) / f__)
        },
    ));
}

fn push_rules_rule_1817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1817,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/f \\[Star] Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f)^q*(a+c*x^(2*k*n)/f)^p,x],x,(f*x)^(1/k)]] /;
        FreeQ[{a,c,d,e,f,p,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&k * &n_) / &f__).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * &k * &n_) / &f__).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&f__ * x_).pow(Atom::num(1) / Atom::num(k_i));

            rubi_star(k, rubi_subst(&transformed, sub, replacement) / f__)
        },
    ));
}

fn push_rules_rule_1818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1818,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) +
          n*p/(f^n*(m+1)*(m+n*(2*p+1)+1)) \\[Star] Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)*
              Simp[2*a*e*(m+1)-b*d*(m+n*(2*p+1)+1)+(b*e*(m+1)-2*c*d*(m+n*(2*p+1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && NeQ[m+n*(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Trinomial recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = (&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p_)
                * (&d__ * &balance + &e__ * (&m_ + 1) * x_.pow(&n_))
                / (&f__ * (&m_ + 1) * &balance);
            let simp_payload = Atom::num(2) * &a__ * &e__ * (&m_ + 1) - &b__ * &d__ * &balance
                + (&b__ * &e__ * (&m_ + 1) - Atom::num(2) * &c__ * &d__ * &balance) * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_ + &n_)
                * trinomial.pow(&p_ - 1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(&n_ * &p_ / (f__.pow(&n_) * (&m_ + 1) * balance), recursive)
        },
    ));
}

fn push_rules_rule_1819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1819,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) +
          2*n*p/(f^n*(m+1)*(m+n*(2*p+1)+1)) \\[Star] Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)*(a*e*(m+1)-c*d*(m+n*(2*p+1)+1)*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && NeQ[m+n*(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Trinomial recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = (&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p_)
                * (&d__ * &balance + &e__ * (&m_ + 1) * x_.pow(&n_))
                / (&f__ * (&m_ + 1) * &balance);
            let recursive_integrand = (&f__ * x_).pow(&m_ + &n_)
                * trinomial.pow(&p_ - 1)
                * (&a__ * &e__ * (&m_ + 1) - &c__ * &d__ * &balance * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(
                    Atom::num(2) * &n_ * &p_
                        / (f__.pow(&n_) * (&m_ + 1) * balance),
                    recursive,
                ) + rubi_simp(&(direct), x_)
        },
    ));
}

fn push_rules_rule_1820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1820,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(b*e*n*p+c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/
            (c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) +
          n*p/(c*(2*n*p+m+1)*(m+n*(2*p+1)+1)) \\[Star] Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p-1)*
            Simp[2*a*c*d*(m+n*(2*p+1)+1)-a*b*e*(m+1)+(2*a*c*e*(2*n*p+m+1)+b*c*d*(m+n*(2*p+1)+1)-b^2*e*(m+n*p+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] && NeQ[2*n*p+m+1,0] && NeQ[m+n*(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Trinomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let balance2 = Atom::num(2) * &n_ * &p_ + &m_ + 1;
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && neq!(balance2, 0)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let balance2 = Atom::num(2) * &n_ * &p_ + &m_ + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = (&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p_)
                * (&b__ * &e__ * &n_ * &p_ + &c__ * &d__ * &balance + &c__ * &e__ * &balance2 * x_.pow(&n_))
                / (&c__ * &f__ * &balance2 * &balance);
            let simp_payload = Atom::num(2) * &a__ * &c__ * &d__ * &balance - &a__ * &b__ * &e__ * (&m_ + 1)
                + (Atom::num(2) * &a__ * &c__ * &e__ * &balance2 + &b__ * &c__ * &d__ * &balance
                    - b__.pow(2) * &e__ * (&m_ + &n_ * &p_ + 1))
                    * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p_ - 1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(&n_ * &p_ / (&c__ * balance2 * balance), recursive)
        },
    ));
}

fn push_rules_rule_1821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1821,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+c*x^(2*n))^p*(c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/(c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) +
          2*a*n*p/((2*n*p+m+1)*(m+n*(2*p+1)+1)) \\[Star] Int[(f*x)^m*(a+c*x^(2*n))^(p-1)*Simp[d*(m+n*(2*p+1)+1)+e*(2*n*p+m+1)*x^n,x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0] && GtQ[p,0] && NeQ[2*n*p+m+1,0] && NeQ[m+n*(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Trinomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let balance2 = Atom::num(2) * &n_ * &p_ + &m_ + 1;
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && neq!(balance2, 0)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let balance2 = Atom::num(2) * &n_ * &p_ + &m_ + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = (&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p_)
                * (&c__ * &d__ * &balance + &c__ * &e__ * &balance2 * x_.pow(&n_))
                / (&c__ * &f__ * &balance2 * &balance);
            let simp_payload = &d__ * &balance + &e__ * &balance2 * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p_ - 1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &a__ * &n_ * &p_ / (balance2 * balance), recursive)
        },
    ));
}

fn push_rules_rule_1822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1822,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(b*d-2*a*e-(b*e-2*c*d)*x^n)/(n*(p+1)*(b^2-4*a*c)) +
          f^n/(n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)*
              Simp[(n-m-1)*(b*d-2*a*e)+(2*n*p+2*n+m+1)*(b*e-2*c*d)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,n-1] && IntegerQ[p]",
        desc: "Trinomial recurrence 2a",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, &n_ - 1)
                && integerq!(p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let raised_balance = Atom::num(2) * &n_ * &p_ + Atom::num(2) * &n_ + &m_ + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = f__.pow(&n_ - 1)
                * (&f__ * x_).pow(&m_ - &n_ + 1)
                * trinomial.pow(&p_ + 1)
                * (&b__ * &d__ - Atom::num(2) * &a__ * &e__
                    - (&b__ * &e__ - Atom::num(2) * &c__ * &d__) * x_.pow(&n_))
                / (&n_ * (&p_ + 1) * &discriminant);
            let simp_payload = (&n_ - &m_ - 1) * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)
                + &raised_balance * (&b__ * &e__ - Atom::num(2) * &c__ * &d__) * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_ - &n_)
                * trinomial.pow(&p_ + 1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(f__.pow(&n_), recursive / (&n_ * (&p_ + 1) * discriminant))
        },
    ));
}

fn push_rules_rule_1823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1823,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
          f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)*(a*e-c*d*x^n)/(2*a*c*n*(p+1)) +
          f^n/(2*a*c*n*(p+1)) \\[Star] Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)*(a*e*(n-m-1)+c*d*(2*n*p+2*n+m+1)*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,n-1] && IntegerQ[p]",
        desc: "Trinomial recurrence 2a",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, &n_ - 1)
                && integerq!(p_)
        },
        rhs: {
            let raised_balance = Atom::num(2) * &n_ * &p_ + Atom::num(2) * &n_ + &m_ + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = f__.pow(&n_ - 1)
                * (&f__ * x_).pow(&m_ - &n_ + 1)
                * trinomial.pow(&p_ + 1)
                * (&a__ * &e__ - &c__ * &d__ * x_.pow(&n_))
                / (Atom::num(2) * &a__ * &c__ * &n_ * (&p_ + 1));
            let recursive_integrand = (&f__ * x_).pow(&m_ - &n_)
                * trinomial.pow(&p_ + 1)
                * (&a__ * &e__ * (&n_ - &m_ - 1) + &c__ * &d__ * &raised_balance * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(f__.pow(&n_), recursive / (Atom::num(2) * &a__ * &c__ * &n_ * (&p_ + 1)))
        },
    ));
}

fn push_rules_rule_1824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1824,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
              Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+c*(m+n*(2*p+3)+1)*(b*d-2*a*e)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] && IntegerQ[p]",
        desc: "Trinomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && integerq!(p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p1 = &p_ + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = -(&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p1)
                * (&d__ * (b__.pow(2) - Atom::num(2) * &a__ * &c__) - &a__ * &b__ * &e__
                    + (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * &c__ * x_.pow(&n_))
                / (&a__ * &f__ * &n_ * &p1 * &discriminant);
            let simp_payload = &d__
                * (b__.pow(2) * (&m_ + &n_ * &p1 + 1)
                    - Atom::num(2) * &a__ * &c__ * (&m_ + Atom::num(2) * &n_ * &p1 + 1))
                - &a__ * &b__ * &e__ * (&m_ + 1)
                + &c__
                    * (&m_ + &n_ * (Atom::num(2) * &p_ + 3) + 1)
                    * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)
                    * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&a__ * &n_ * p1 * discriminant), recursive)
        },
    ));
}

fn push_rules_rule_1825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1825,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) +
          1/(2*a*n*(p+1)) \\[Star] Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0] && LtQ[p,-1] && IntegerQ[p]",
        desc: "Trinomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && integerq!(p_)
        },
        rhs: {
            let p1 = &p_ + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = -(&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p1)
                * (&d__ + &e__ * x_.pow(&n_))
                / (Atom::num(2) * &a__ * &f__ * &n_ * &p1);
            let simp_payload =
                &d__ * (&m_ + Atom::num(2) * &n_ * &p1 + 1) + &e__ * (&m_ + &n_ * (Atom::num(2) * &p_ + 3) + 1) * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (Atom::num(2) * &a__ * &n_ * p1), recursive)
        },
    ));
}

fn push_rules_rule_1826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1826,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          e*f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) -
          f^n/(c*(m+n(2*p+1)+1)) \\[Star]
            Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m-n+1)+(b*e*(m+n*p+1)-c*d*(m+n(2*p+1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[m,n-1] && NeQ[m+n(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(m_, &n_ - 1)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct =
                &e__ * f__.pow(&n_ - 1) * (&f__ * x_).pow(&m_ - &n_ + 1) * trinomial.pow(&p_ + 1) / (&c__ * &balance);
            let simp_payload = &a__ * &e__ * (&m_ - &n_ + 1)
                + (&b__ * &e__ * (&m_ + &n_ * &p_ + 1) - &c__ * &d__ * &balance) * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_ - &n_) * trinomial.pow(&p_) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(f__.pow(&n_), recursive / (&c__ * balance))
        },
    ));
}

fn push_rules_rule_1827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1827,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          e*f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) -
          f^n/(c*(m+n(2*p+1)+1)) \\[Star] Int[(f*x)^(m-n)*(a+c*x^(2*n))^p*(a*e*(m-n+1)-c*d*(m+n(2*p+1)+1)*x^n),x] /;
        FreeQ[{a,c,d,e,f,p},x] && EqQ[n2,2*n] && IGtQ[n,0] && GtQ[m,n-1] && NeQ[m+n(2*p+1)+1,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            freeq!([a__, c__, d__, e__, f__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && gtq!(m_, &n_ - 1)
                && neq!(balance, 0)
                && integerq!(p_)
        },
        rhs: {
            let balance = &m_ + &n_ * (Atom::num(2) * &p_ + 1) + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct =
                &e__ * f__.pow(&n_ - 1) * (&f__ * x_).pow(&m_ - &n_ + 1) * trinomial.pow(&p_ + 1) / (&c__ * &balance);
            let recursive_integrand = (&f__ * x_).pow(&m_ - &n_)
                * trinomial.pow(&p_)
                * (&a__ * &e__ * (&m_ - &n_ + 1) - &c__ * &d__ * &balance * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(f__.pow(&n_), recursive / (&c__ * balance))
        },
    ));
}

fn push_rules_rule_1828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1828,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          d*(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*f*(m+1)) +
          1/(a*f^n*(m+1)) \\[Star] Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m+1)-b*d*(m+n*(p+1)+1)-c*d*(m+2*n(p+1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[m,-1] && IntegerQ[p]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && integerq!(p_)
        },
        rhs: {
            let m1 = &m_ + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = &d__ * (&f__ * x_).pow(&m1) * trinomial.pow(&p_ + 1) / (&a__ * &f__ * &m1);
            let simp_payload = &a__ * &e__ * &m1
                - &b__ * &d__ * (&m_ + &n_ * (&p_ + 1) + 1)
                - &c__ * &d__ * (&m_ + Atom::num(2) * &n_ * (&p_ + 1) + 1) * x_.pow(&n_);
            let recursive_integrand =
                (&f__ * x_).pow(&m_ + &n_) * trinomial.pow(&p_) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&a__ * f__.pow(&n_) * m1), recursive)
        },
    ));
}

fn push_rules_rule_1829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1829,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          d*(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)/(a*f*(m+1)) +
          1/(a*f^n*(m+1)) \\[Star] Int[(f*x)^(m+n)*(a+c*x^(2*n))^p*(a*e*(m+1)-c*d*(m+2*n(p+1)+1)*x^n),x] /;
        FreeQ[{a,c,d,e,f,p},x] && EqQ[n2,2*n] && IGtQ[n,0] && LtQ[m,-1] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && integerq!(p_)
        },
        rhs: {
            let m1 = &m_ + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = &d__ * (&f__ * x_).pow(&m1) * trinomial.pow(&p_ + 1) / (&a__ * &f__ * &m1);
            let recursive_integrand = (&f__ * x_).pow(&m_ + &n_)
                * trinomial.pow(&p_)
                * (&a__ * &e__ * &m1 - &c__ * &d__ * (&m_ + Atom::num(2) * &n_ * (&p_ + 1) + 1) * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&a__ * f__.pow(&n_) * m1), recursive)
        },
    ));
}

fn push_rules_rule_1830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1830,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a*c,2]},
          With[{r=Rt[2*c*q-b*c,2]},
          c/(2*q*r) \\[Star] Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] +
          c/(2*q*r) \\[Star] Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
         Not[LtQ[2*c*q-b*c,0]]] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && LtQ[b^2-4*a*c,0] && IntegersQ[m,n/2] && LtQ[0,m,n] && PosQ[a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [f__, e__, b__, c__],
        when: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let radicand = Atom::num(2) * &c__ * &q_rt - &b__ * &c__;
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && ltq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integersq!([m_, &n_ / Atom::num(2)])
                && gtq!(m_, 0)
                && ltq!(m_, n_)
                && posq!(&a__ * &c__)
                && !ltq!(radicand, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let r_rt = rubi_rt(&(Atom::num(2) * &c__ * &q_rt - &b__ * &c__), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let coefficient = &c__ / (Atom::num(2) * &q_rt * &r_rt);
            let first_simp = rubi_simp(&(&d__ * &r_rt - (&c__ * &d__ - &e__ * &q_rt) * &half_power), x_);
            let second_simp = rubi_simp(&(&d__ * &r_rt + (&c__ * &d__ - &e__ * &q_rt) * &half_power), x_);
            let first_integrand = (&f__ * x_).pow(&m_) * first_simp
                / (&q_rt - &r_rt * &half_power + &c__ * x_.pow(&n_));
            let second_integrand = (&f__ * x_).pow(&m_) * second_simp
                / (&q_rt + &r_rt * &half_power + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first)
                    + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1831,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a*c,2]},
          With[{r=Rt[2*c*q,2]},
          c/(2*q*r) \\[Star] Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] +
          c/(2*q*r) \\[Star] Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
         Not[LtQ[2*c*q,0]]] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && GtQ[a*c,0] && IntegersQ[m,n/2] && LtQ[0,m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, x_],
        optional: [f__, e__, c__],
        when: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let radicand = Atom::num(2) * &c__ * &q_rt;
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && gtq!(&a__ * &c__, 0)
                && integersq!([m_, &n_ / Atom::num(2)])
                && gtq!(m_, 0)
                && ltq!(m_, n_)
                && !ltq!(radicand, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let r_rt = rubi_rt(&(Atom::num(2) * &c__ * &q_rt), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let coefficient = &c__ / (Atom::num(2) * &q_rt * &r_rt);
            let first_simp = rubi_simp(&(&d__ * &r_rt - (&c__ * &d__ - &e__ * &q_rt) * &half_power), x_);
            let second_simp = rubi_simp(&(&d__ * &r_rt + (&c__ * &d__ - &e__ * &q_rt) * &half_power), x_);
            let first_integrand = (&f__ * x_).pow(&m_) * first_simp
                / (&q_rt - &r_rt * &half_power + &c__ * x_.pow(&n_));
            let second_integrand = (&f__ * x_).pow(&m_) * second_simp
                / (&q_rt + &r_rt * &half_power + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first)
                    + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1832,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a*c,2]},
          With[{r=Rt[2*c*q-b*c,2]},
          c/(2*q*r) \\[Star] Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] +
          c/(2*q*r) \\[Star] Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
         Not[LtQ[2*c*q-b*c,0]]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && LtQ[b^2-4*a*c,0] && IGtQ[n/2,1] && PosQ[a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let radicand = Atom::num(2) * &c__ * &q_rt - &b__ * &c__;
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && ltq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&n_ / Atom::num(2), 1)
                && posq!(&a__ * &c__)
                && !ltq!(radicand, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let r_rt = rubi_rt(&(Atom::num(2) * &c__ * &q_rt - &b__ * &c__), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let coefficient = &c__ / (Atom::num(2) * &q_rt * &r_rt);
            let first_integrand = (&f__ * x_).pow(&m_) * (&d__ * &r_rt - (&c__ * &d__ - &e__ * &q_rt) * &half_power)
                / (&q_rt - &r_rt * &half_power + &c__ * x_.pow(&n_));
            let second_integrand = (&f__ * x_).pow(&m_) * (&d__ * &r_rt + (&c__ * &d__ - &e__ * &q_rt) * &half_power)
                / (&q_rt + &r_rt * &half_power + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first)
                    + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1833,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a*c,2]},
          With[{r=Rt[2*c*q,2]},
          c/(2*q*r) \\[Star] Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] +
          c/(2*q*r) \\[Star] Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
         Not[LtQ[2*c*q,0]]] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n/2,1] && GtQ[a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let radicand = Atom::num(2) * &c__ * &q_rt;
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(&n_ / Atom::num(2), 1)
                && gtq!(&a__ * &c__, 0)
                && !ltq!(radicand, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(&a__ * &c__), 2);
            let r_rt = rubi_rt(&(Atom::num(2) * &c__ * &q_rt), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let coefficient = &c__ / (Atom::num(2) * &q_rt * &r_rt);
            let first_integrand = (&f__ * x_).pow(&m_) * (&d__ * &r_rt - (&c__ * &d__ - &e__ * &q_rt) * &half_power)
                / (&q_rt - &r_rt * &half_power + &c__ * x_.pow(&n_));
            let second_integrand = (&f__ * x_).pow(&m_) * (&d__ * &r_rt + (&c__ * &d__ - &e__ * &q_rt) * &half_power)
                / (&q_rt + &r_rt * &half_power + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first)
                    + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1834,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[(f*x)^m/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[(f*x)^m/(b/2+q/2+c*x^n),x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let split = (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &q_rt);
            let first_integrand =
                (&f__ * x_).pow(&m_) / (&b__ / Atom::num(2) - &q_rt / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand =
                (&f__ * x_).pow(&m_) / (&b__ / Atom::num(2) + &q_rt / Atom::num(2) + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__ / Atom::num(2) + &split, first) + rubi_star(&e__ / Atom::num(2) - split, second)
        },
    ));
}

fn push_rules_rule_1835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1835,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          -(e/2+c*d/(2*q)) \\[Star] Int[(f*x)^m/(q-c*x^n),x] + (e/2-c*d/(2*q)) \\[Star] Int[(f*x)^m/(q+c*x^n),x]] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
        },
        rhs: {
            let q_rt = rubi_rt(&(-&a__ * &c__), 2);
            let split = &c__ * &d__ / (Atom::num(2) * &q_rt);
            let first_integrand = (&f__ * x_).pow(&m_) / (&q_rt - &c__ * x_.pow(&n_));
            let second_integrand = (&f__ * x_).pow(&m_) / (&q_rt + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-(&e__ / Atom::num(2) + &split), first) + rubi_star(&e__ / Atom::num(2) - split, second)
        },
    ));
}

fn push_rules_rule_1836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1836,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IntegerQ[q] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1837,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0] && IntegerQ[q] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1838,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IntegerQ[q] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && integerq!(q_)
                && !integerq!(m_)
        },
        rhs: {
            let u = (&f__ * x_).pow(&m_);
            let v_payload = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1839,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0] && IntegerQ[q] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && integerq!(q_)
                && !integerq!(m_)
        },
        rhs: {
            let u = (&f__ * x_).pow(&m_);
            let v_payload =
                (&d__ + &e__ * x_.pow(&n_)).pow(&q_) / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1840,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          f^(2*n)/c^2 \\[Star] Int[(f*x)^(m-2*n)*(c*d-b*e+c*e*x^n)*(d+e*x^n)^(q-1),x] -
          f^(2*n)/c^2 \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^(q-1)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,2*n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let coefficient = f__.pow(Atom::num(2) * &n_) / c__.pow(2);
            let base = &d__ + &e__ * x_.pow(&n_);
            let denominator = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let first_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * (&c__ * &d__ - &b__ * &e__ + &c__ * &e__ * x_.pow(&n_))
                * base.pow(&q_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload =
                &a__ * (&c__ * &d__ - &b__ * &e__) + (&b__ * &c__ * &d__ - b__.pow(2) * &e__ + &a__ * &c__ * &e__) * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * base.pow(&q_ - 1)
                * rubi_simp(&simp_payload, x_)
                / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1841,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          f^(2*n)/c \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] -
          a*f^(2*n)/c \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^q/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let coefficient = f__.pow(Atom::num(2) * &n_) / &c__;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * base.pow(&q_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first) - rubi_star(&a__ * coefficient, second)
        },
    ));
}

fn push_rules_rule_1842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1842,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          e*f^n/c \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] -
          f^n/c \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-(c*d-b*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,n-1] && LeQ[m,2n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, &n_ - 1)
                && leq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let coefficient = &e__ * f__.pow(&n_) / &c__;
            let second_coefficient = f__.pow(&n_) / &c__;
            let base = &d__ + &e__ * x_.pow(&n_);
            let denominator = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let first_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &e__ - (&c__ * &d__ - &b__ * &e__) * x_.pow(&n_);
            let second_integrand =
                (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_ - 1) * rubi_simp(&simp_payload, x_) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(coefficient, first) - rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1843,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          e*f^n/c \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] -
          f^n/c \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,n-1] && LeQ[m,2n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, &n_ - 1)
                && leq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let coefficient = &e__ * f__.pow(&n_) / &c__;
            let second_coefficient = f__.pow(&n_) / &c__;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &e__ - &c__ * &d__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_ - 1) * rubi_simp(&simp_payload, x_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(coefficient, first) - rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1844,
        source: "Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          d/a \\[Star] Int[(f*x)^m*(d+e*x^n)^(q-1),x] -
          1/(a*f^n) \\[Star] Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[b*d-a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, d__, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_) * base.pow(&q_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &b__ * &d__ - &a__ * &e__ + &c__ * &d__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ + &n_) * base.pow(&q_ - 1) * rubi_simp(&simp_payload, x_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__, first / &a__) - rubi_star(Atom::num(1) / (&a__ * f__.pow(&n_)), second)
        },
    ));
}

fn push_rules_rule_1845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1845,
        source: "Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          d/a \\[Star] Int[(f*x)^m*(d+e*x^n)^(q-1),x] +
          1/(a*f^n) \\[Star] Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, d__, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_) * base.pow(&q_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &e__ - &c__ * &d__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ + &n_) * base.pow(&q_ - 1) * rubi_simp(&simp_payload, x_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__, first / &a__) + rubi_star(Atom::num(1) / (&a__ * f__.pow(&n_)), second)
        },
    ));
}

fn push_rules_rule_1846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1846,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] -
          f^(2*n)/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*Simp[a*d+(b*d-a*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,2*n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let coefficient = f__.pow(Atom::num(2) * &n_) / &denominator;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * base.pow(&q_ + 1)
                * rubi_simp(&simp_payload, x_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) * &coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1847,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          d^2*f^(2*n)/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] -
          a*f^(2*n)/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let coefficient = f__.pow(Atom::num(2) * &n_) / &denominator;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * base.pow(&q_ + 1)
                * (&d__ - &e__ * x_.pow(&n_))
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) * &coefficient, first) - rubi_star(&a__ * coefficient, second)
        },
    ));
}

fn push_rules_rule_1848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1848,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          -d*e*f^n/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^q,x] +
          f^n/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,n-1] && LeQ[m,2*n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, &n_ - 1)
                && leq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let coefficient = f__.pow(&n_) / &denominator;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &e__ + &c__ * &d__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ - &n_)
                * base.pow(&q_ + 1)
                * rubi_simp(&simp_payload, x_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&d__ * &e__ * &coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1849,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          -d*e*f^n/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^q,x] +
          f^n/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,n-1] && LeQ[m,2*n-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, d__, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, &n_ - 1)
                && leq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let coefficient = f__.pow(&n_) / &denominator;
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &a__ * &e__ + &c__ * &d__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_ - &n_) * base.pow(&q_ + 1) * rubi_simp(&simp_payload, x_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&d__ * &e__ * &coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1850,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          e^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^n)^q,x] +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^n)^(q+1)*Simp[c*d-b*e-c*e*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp_payload = &c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(&n_);
            let second_integrand = (&f__ * x_).pow(&m_)
                * base.pow(&q_ + 1)
                * rubi_simp(&simp_payload, x_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__.pow(2), first / &denominator) + rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_1851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1851,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
          e^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^n)^q,x] +
          c/(c*d^2+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let base = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_) * base.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_)
                * base.pow(&q_ + 1)
                * (&d__ - &e__ * x_.pow(&n_))
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__.pow(2), first / &denominator) + rubi_star(c__, second / denominator)
        },
    ));
}

fn push_rules_rule_1852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1852,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,f,q,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let v_payload =
                (&f__ * x_).pow(&m_) / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1853,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,f,q,n},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, q_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let v_payload = (&f__ * x_).pow(&m_) / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1854,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[IntegerQ[q]] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && !integerq!(m_)
        },
        rhs: {
            let u = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let v_payload = Atom::num(1) / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1855,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,f,m,q,n},x] && EqQ[n2,2*n] && IGtQ[n,0] && Not[IntegerQ[q]] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, q_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && !integerq!(q_)
                && !integerq!(m_)
        },
        rhs: {
            let u = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let v_payload = Atom::num(1) / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1856,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
          1/d^2 \\[Star] Int[(f*x)^m*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] +
          (c*d^2-b*d*e+a*e^2)/(d^2*f^(2*n)) \\[Star] Int[(f*x)^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,-n]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, n_, c__, n2_, p_, d__, e__, x_],
        optional: [f__, a__, b__, c__, n2_, p_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, Atom::num(-1) * &n_)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_)
                * (&a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(&n_))
                * trinomial.pow(&p_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                (&f__ * x_).pow(&m_ + Atom::num(2) * &n_) * trinomial.pow(&p_ - 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / d__.pow(2), first) + rubi_star(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), second / (d__.pow(2) * f__.pow(Atom::num(2) * &n_)))
        },
    ));
}

fn push_rules_rule_1857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1857,
        source: "Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
          a/d^2 \\[Star] Int[(f*x)^m*(d-e*x^n)*(a+c*x^(2*n))^(p-1),x] +
          (c*d^2+a*e^2)/(d^2*f^(2*n)) \\[Star] Int[(f*x)^(m+2*n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,-n]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, c__, n2_, p_, d__, e__, n_, x_],
        optional: [f__, c__, n2_, p_, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, Atom::num(-1) * &n_)
        },
        rhs: {
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_) * (&d__ - &e__ * x_.pow(&n_)) * trinomial.pow(&p_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                (&f__ * x_).pow(&m_ + Atom::num(2) * &n_) * trinomial.pow(&p_ - 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&a__, first / d__.pow(2)) + rubi_star(&c__ * d__.pow(2) + &a__ * e__.pow(2), second / (d__.pow(2) * f__.pow(Atom::num(2) * &n_)))
        },
    ));
}

fn push_rules_rule_1858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1858,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
          1/(d*e) \\[Star] Int[(f*x)^m*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] -
          (c*d^2-b*d*e+a*e^2)/(d*e*f^n) \\[Star] Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, n_, c__, n2_, p_, d__, e__, x_],
        optional: [f__, a__, b__, c__, n2_, p_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(&n_)) * trinomial.pow(&p_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ + &n_) * trinomial.pow(&p_ - 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / (&d__ * &e__), first) - rubi_star(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), second / (&d__ * &e__ * f__.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1859,
        source: "Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
          1/(d*e) \\[Star] Int[(f*x)^m*(a*e+c*d*x^n)*(a+c*x^(2*n))^(p-1),x] -
          (c*d^2+a*e^2)/(d*e*f^n) \\[Star] Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, c__, n2_, p_, d__, e__, n_, x_],
        optional: [f__, c__, n2_, p_, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(&n_)) * trinomial.pow(&p_ - 1);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ + &n_) * trinomial.pow(&p_ - 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / (&d__ * &e__), first) - rubi_star(&c__ * d__.pow(2) + &a__ * e__.pow(2), second / (&d__ * &e__ * f__.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1860,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
          -f^(2*n)/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] +
          d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,n]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, n_, c__, n2_, p_, d__, e__, x_],
        optional: [f__, m_, a__, b__, c__, n2_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, n_)
        },
        rhs: {
            let coefficient_denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = (&f__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * (&a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(&n_))
                * trinomial.pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * trinomial.pow(&p_ + 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-f__.pow(Atom::num(2) * &n_), first / &coefficient_denominator)
                    + rubi_star(d__.pow(2) * f__.pow(Atom::num(2) * &n_) / coefficient_denominator, second)
        },
    ));
}

fn push_rules_rule_1861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1861,
        source: "Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
          -a*f^(2*n)/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(d-e*x^n)*(a+c*x^(2*n))^p,x] +
          d^2*f^(2*n)/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2*n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,n]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, c__, n2_, p_, d__, e__, n_, x_],
        optional: [f__, m_, c__, n2_, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, n_)
        },
        rhs: {
            let coefficient_denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * (&d__ - &e__ * x_.pow(&n_)) * trinomial.pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                (&f__ * x_).pow(&m_ - Atom::num(2) * &n_) * trinomial.pow(&p_ + 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&a__ * f__.pow(Atom::num(2) * &n_) / &coefficient_denominator, first)
                    + rubi_star(d__.pow(2) * f__.pow(Atom::num(2) * &n_) / coefficient_denominator, second)
        },
    ));
}

fn push_rules_rule_1862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1862,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
          f^n/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^p,x] -
          d*e*f^n/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, n_, c__, n2_, p_, d__, e__, x_],
        optional: [f__, m_, a__, b__, c__, n2_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let coefficient_denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_ - &n_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(&n_)) * trinomial.pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ - &n_) * trinomial.pow(&p_ + 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(f__.pow(&n_), first / &coefficient_denominator) - rubi_star(&d__ * &e__ * f__.pow(&n_) / coefficient_denominator, second)
        },
    ));
}

fn push_rules_rule_1863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1863,
        source: "Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
          f^n/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+c*x^(2*n))^p,x] -
          d*e*f^n/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[n2,2*n] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["Algebraic expansion"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, c__, n2_, p_, d__, e__, n_, x_],
        optional: [f__, m_, c__, n2_, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let coefficient_denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &d__ + &e__ * x_.pow(&n_);
            let first_integrand =
                (&f__ * x_).pow(&m_ - &n_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(&n_)) * trinomial.pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (&f__ * x_).pow(&m_ - &n_) * trinomial.pow(&p_ + 1) / denominator;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(f__.pow(&n_), first / &coefficient_denominator) - rubi_star(&d__ * &e__ * f__.pow(&n_) / coefficient_denominator, second)
        },
    ));
}

fn push_rules_rule_1864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1864,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let u = (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let v_payload = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let expanded =
                rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1865,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2,2*n] && IGtQ[n,0] && IGtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(n_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let u = (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let v_payload = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1866,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &b__ * sub_atom.pow(-&n_) + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1867,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,c,d,e,p,q},x] && EqQ[n2,2*n] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1868,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[m]},
          -g/f \\[Star] Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+b*f^(-n)*x^(-g*n)+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let g_i = rubi_denominator(&m_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * f__.pow(-&n_) * sub_atom.pow(-&g * &n_)).pow(&q_)
                * (&a__
                    + &b__ * f__.pow(-&n_) * sub_atom.pow(-&g * &n_)
                    + &c__ * f__.pow(Atom::num(-2) * &n_) * sub_atom.pow(Atom::num(-2) * &g * &n_))
                .pow(&p_)
                / sub_atom.pow(&g * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&f__ * x_).pow(Atom::num(1) / &g);

            rubi_star(-&g, rubi_subst(&transformed, sub, replacement) / &f__)
        },
    ));
}

fn push_rules_rule_1869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1869,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[m]},
          -g/f \\[Star] Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
        FreeQ[{a,c,d,e,f,p,q},x] && EqQ[n2,2*n] && ILtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let g_i = rubi_denominator(&m_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * f__.pow(-&n_) * sub_atom.pow(-&g * &n_)).pow(&q_)
                * (&a__ + &c__ * f__.pow(Atom::num(-2) * &n_) * sub_atom.pow(Atom::num(-2) * &g * &n_)).pow(&p_)
                / sub_atom.pow(&g * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&f__ * x_).pow(Atom::num(1) / &g);

            rubi_star(-&g, rubi_subst(&transformed, sub, replacement) / &f__)
        },
    ));
}

fn push_rules_rule_1870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1870,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m] \\[Star] Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && !rational_q(&m_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &b__ * sub_atom.pow(-&n_) + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let coefficient =
                f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) * x_.pow(-1).pow(&frac_m);

            rubi_star(-coefficient, rubi_subst(&transformed, sub, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_1871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1871,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m] \\[Star] Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
                && !rational_q(&m_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let coefficient =
                f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) * x_.pow(-1).pow(&frac_m);

            rubi_star(-coefficient, rubi_subst(&transformed, sub, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_1872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1872,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&g * (&m_ + 1) - 1)
                * (&d__ + &e__ * sub_atom.pow(&g * &n_)).pow(&q_)
                * (&a__ + &b__ * sub_atom.pow(&g * &n_) + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(g, rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / Atom::num(g_i))))
        },
    ));
}

fn push_rules_rule_1873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1873,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,c,d,e,m,p,q},x] && EqQ[n2,2*n] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&g * (&m_ + 1) - 1)
                * (&d__ + &e__ * sub_atom.pow(&g * &n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(g, rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / Atom::num(g_i))))
        },
    ));
}

fn push_rules_rule_1874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1874,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1875,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1876,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[RationalQ[n]] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_],
        when: {
            let m1 = &m_ + 1;

            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !rationalq!(n_)
                && neq!(m1, 0)
                && integerq!(rubi_simplify(&(&n_ / &m1)))
                && !integerq!(n_)
        },
        rhs: {
            let k = rubi_simplify(&(&n_ / (&m_ + 1)));
            let k2 = rubi_simplify(&(Atom::num(2) * &n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&d__ + &e__ * sub_atom.pow(&k)).pow(&q_) * (&a__ + &b__ * sub_atom.pow(&k) + &c__ * sub_atom.pow(&k2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(&transformed, sub, x_.pow(&m_ + 1)))
        },
    ));
}

fn push_rules_rule_1877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1877,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && Not[RationalQ[n]] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_],
        when: {
            let m1 = &m_ + 1;

            freeq!([a__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
                && neq!(m1, 0)
                && integerq!(rubi_simplify(&(&n_ / &m1)))
                && !integerq!(n_)
        },
        rhs: {
            let k = rubi_simplify(&(&n_ / (&m_ + 1)));
            let k2 = rubi_simplify(&(Atom::num(2) * &n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(&k)).pow(&q_) * (&a__ + &c__ * sub_atom.pow(&k2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(&transformed, sub, x_.pow(&m_ + 1)))
        },
    ));
}

fn push_rules_rule_1878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1878,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[RationalQ[n]] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: {
            let k = rubi_simplify(&(&n_ / (&m_ + 1)));

            freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !rationalq!(n_)
                && integerq!(&k)
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = f__.pow(rubi_int_part(&m_))
                * (&f__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1879,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2,2*n] && Not[RationalQ[n]] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__, n2_],
        x_free: [a__, c__, d__, e__, f__, m_, p_, q_],
        when: {
            let k = rubi_simplify(&(&n_ / (&m_ + 1)));

            freeq!([a__, c__, d__, e__, f__, m_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
                && integerq!(&k)
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = f__.pow(rubi_int_part(&m_))
                * (&f__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1880,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          2*c/r \\[Star] Int[(f*x)^m*(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r \\[Star] Int[(f*x)^m*(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
        FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[RationalQ[n]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [f__, m_, e__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !rationalq!(n_)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let numerator = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let first_integrand = &numerator / (&b__ - &r + Atom::num(2) * &c__ * x_.pow(&n_));
            let second_integrand = numerator / (&b__ + &r + Atom::num(2) * &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(2) * &c__ / &r;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1881,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
          With[{r=Rt[-a*c,2]},
          -c/(2*r) \\[Star] Int[(f*x)^m*(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r) \\[Star] Int[(f*x)^m*(d+e*x^n)^q/(r+c*x^n),x]] /;
        FreeQ[{a,c,d,e,f,m,n,q},x] && EqQ[n2,2*n] && Not[RationalQ[n]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [f__, m_, e__, c__, n2_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
        },
        rhs: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            let numerator = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(&n_)).pow(&q_);
            let first_integrand = &numerator / (&r - &c__ * x_.pow(&n_));
            let second_integrand = numerator / (&r + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &c__ / (Atom::num(2) * &r);

            rubi_star(-&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1882,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
              Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+(m+n*(2*p+3)+1)*(b*d-2*a*e)*c*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[RationalQ[n]] && ILtQ[p+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !rationalq!(n_)
                && iltq!(&p_ + 1, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p1 = &p_ + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = -(&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p1)
                * (&d__ * (b__.pow(2) - Atom::num(2) * &a__ * &c__) - &a__ * &b__ * &e__
                    + (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * &c__ * x_.pow(&n_))
                / (&a__ * &f__ * &n_ * &p1 * &discriminant);
            let simp_payload = &d__
                * (b__.pow(2) * (&m_ + &n_ * &p1 + 1)
                    - Atom::num(2) * &a__ * &c__ * (&m_ + Atom::num(2) * &n_ * &p1 + 1))
                - &a__ * &b__ * &e__ * (&m_ + 1)
                + (&m_ + &n_ * (Atom::num(2) * &p_ + 3) + 1)
                    * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)
                    * &c__
                    * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&a__ * &n_ * p1 * discriminant), recursive)
        },
    ));
}

fn push_rules_rule_1883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1883,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) +
          1/(2*a*n*(p+1)) \\[Star] Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
        FreeQ[{a,c,d,e,f,m,n},x] && EqQ[n2,2*n] && Not[RationalQ[n]] && ILtQ[p+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
                && iltq!(&p_ + 1, 0)
        },
        rhs: {
            let p1 = &p_ + 1;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = -(&f__ * x_).pow(&m_ + 1)
                * trinomial.pow(&p1)
                * (&d__ + &e__ * x_.pow(&n_))
                / (Atom::num(2) * &a__ * &f__ * &n_ * &p1);
            let simp_payload =
                &d__ * (&m_ + Atom::num(2) * &n_ * &p1 + 1) + &e__ * (&m_ + &n_ * (Atom::num(2) * &p_ + 3) + 1) * x_.pow(&n_);
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * trinomial.pow(&p1)
                * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (Atom::num(2) * &a__ * &n_ * p1), recursive)
        },
    ));
}

fn push_rules_rule_1884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1884,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && Not[RationalQ[n]] && (IGtQ[p,0] || IGtQ[q,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !rationalq!(n_)
                && (igtq!(p_, 0) || igtq!(q_, 0))
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1885,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && Not[RationalQ[n]] && (IGtQ[p,0] || IGtQ[q,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
                && (igtq!(p_, 0) || igtq!(q_, 0))
        },
        rhs: {
            let expand_integrand_payload = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1886,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          (f*x)^m/x^m \\[Star] Int[ExpandIntegrand[x^m*(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
        FreeQ[{a,c,d,e,f,m,n,p},x] && EqQ[n2,2*n] && Not[RationalQ[n]] && Not[IntegerQ[p]] && ILtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !rationalq!(n_)
                && !integerq!(p_)
                && iltq!(q_, 0)
        },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(Atom::num(2) * &n_);
            let u = x_.pow(&m_) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let v_payload = (&d__ / &denominator - &e__ * x_.pow(&n_) / denominator).pow(-&q_);
            let expanded = rubi_expand_integrand_product(&u, &v_payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            let coefficient = (&f__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1887,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__
                    + &b__ * x_.pow(&n_)
                    + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1888,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [f__, m_, e__, q_, c__, n2_, p_],
        x_free: [a__, c__, d__, e__, f__, m_, n_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, n2_, p_, q_, u__, w__);
    rules.push(rubi_rule!(
        order: 1889,
        source: "Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x] && NeQ[v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u__.pow(m_)
            * (d__ + e__ * w__.pow(n_)).pow(q_)
            * (a__ + b__ * w__.pow(n_) + c__ * w__.pow(n2_)).pow(p_),
        with: [u__, m_, d__, e__, w__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, b__, c__, n2_, p_],
        x_dep: [u__, w__],
        x_free: [a__, b__, c__, d__, e__, m_, n_, p_, q_],
        x_linear: [u__, w__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_linear_pair_q(&u__, &w__, x_)
                && neq!(w__, x_)
        },
        rhs: {
            let coefficient = rubi_coeff(&w__, x_, 1).rubi_rhs();
            let denominator = &coefficient * w__.pow(&m_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&d__ + &e__ * sub_atom.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * sub_atom.pow(&n_) + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(u__.pow(&m_), rubi_subst(&transformed, sub, &w__) / denominator)
        },
    ));
}

fn push_rules_rule_1890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, m_, n_, n2_, p_, q_, u__, w__);
    rules.push(rubi_rule!(
        order: 1890,
        source: "Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,v] /;
        FreeQ[{a,c,d,e,m,n,p},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x] && NeQ[v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u__.pow(m_) * (d__ + e__ * w__.pow(n_)).pow(q_) * (a__ + c__ * w__.pow(n2_)).pow(p_),
        with: [u__, m_, d__, e__, w__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, q_, c__, n2_, p_],
        x_dep: [u__, w__],
        x_free: [a__, c__, d__, e__, m_, n_, p_],
        x_linear: [u__, w__],
        when: {
            freeq!([a__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_linear_pair_q(&u__, &w__, x_)
                && neq!(w__, x_)
        },
        rhs: {
            let coefficient = rubi_coeff(&w__, x_, 1).rubi_rhs();
            let denominator = &coefficient * w__.pow(&m_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow(&m_) * (&d__ + &e__ * sub_atom.pow(&n_)).pow(&q_) * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(u__.pow(&m_), rubi_subst(&transformed, sub, &w__) / denominator)
        },
    ));
}

fn push_rules_rule_1891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1891,
        source: "Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(m-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [m_, d__, e__, mn_, q_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, e__, mn_, q_, a__, b__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(mn_, -&n_)
                && integerq!(q_)
                && (posq!(n_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * (&e__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, mn_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1892,
        source: "Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(m+mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
        FreeQ[{a,c,d,e,m,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q] && (PosQ[n2] || Not[IntegerQ[p]])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, d__, e__, mn_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, mn_, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, m_, mn_, p_], x_)
                && eqq!(n2_, Atom::num(-2) * &mn_)
                && integerq!(q_)
                && (posq!(n2_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + &mn_ * &q_)
                * (&e__ + &d__ * x_.pow(-&mn_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(&n2_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1893,
        source: "Int[x_^m_.*(d_+e_.*x_^n_.)^q_.*(a_.+b_.*x_^mn_.+c_.*x_^mn2_.)^p_.,x_Symbol] :=
          Int[x^(m-2*n*p)*(d+e*x^n)^q*(c+b*x^n+a*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[mn,-n] && EqQ[mn2,2*mn] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, mn_, c__, mn2_, p_, x_],
        optional: [m_, e__, n_, q_, a__, b__, mn_, c__, mn2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_], x_)
                && eqq!(mn_, -&n_)
                && eqq!(mn2_, Atom::num(2) * &mn_)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - Atom::num(2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&c__ + &b__ * x_.pow(&n_) + &a__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1894,
        source: "Int[x_^m_.*(d_+e_.*x_^n_.)^q_.*(a_.+c_.*x_^mn2_.)^p_.,x_Symbol] :=
          Int[x^(m-2*n*p)*(d+e*x^n)^q*(c+a*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,m,n,q},x] && EqQ[mn2,-2*n] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, mn2_, p_, x_],
        optional: [m_, e__, n_, q_, a__, c__, mn2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, m_, n_, q_], x_)
                && eqq!(mn2_, Atom::num(-2) * &n_)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - Atom::num(2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&c__ + &a__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1895,
        source: "Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          e^IntPart[q]*x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(1+d*x^n/e)^FracPart[q] \\[Star] Int[x^(m-n*q)*(1+d*x^n/e)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [m_, d__, e__, mn_, q_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, e__, mn_, a__, b__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(mn_, -&n_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
        },
        rhs: {
            if e__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_q = rubi_frac_part(&q_);
            let normalized = Atom::num(1) + &d__ * x_.pow(&n_) / &e__;
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * normalized.pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&q_)) * x_.pow(&n_ * &frac_q) * (&d__ + &e__ * x_.pow(-&n_)).pow(&frac_q) / normalized.pow(frac_q), recursive)
        },
    ));
}

fn push_rules_rule_1896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, mn_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1896,
        source: "Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          e^IntPart[q]*x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(1+d*x^(-mn)/e)^FracPart[q] \\[Star] Int[x^(m+mn*q)*(1+d*x^(-mn)/e)^q*(a+c*x^n2)^p,x] /;
        FreeQ[{a,c,d,e,m,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, d__, e__, mn_, q_, a__, c__, n2_, p_, x_],
        optional: [m_, e__, mn_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, m_, mn_, p_, q_], x_)
                && eqq!(n2_, Atom::num(-2) * &mn_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n2_)
        },
        rhs: {
            if e__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_q = rubi_frac_part(&q_);
            let normalized = Atom::num(1) + &d__ * x_.pow(-&mn_) / &e__;
            let recursive_integrand = x_.pow(&m_ + &mn_ * &q_)
                * normalized.pow(&q_)
                * (&a__ + &c__ * x_.pow(&n2_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&q_)) * x_.pow(-&mn_ * &frac_q) * (&d__ + &e__ * x_.pow(&mn_)).pow(&frac_q) / normalized.pow(frac_q), recursive)
        },
    ));
}

fn push_rules_rule_1897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1897,
        source: "Int[x_^m_.*(d_+e_.*x_^n_.)^q_.*(a_.+b_.*x_^mn_.+c_.*x_^mn2_.)^p_,x_Symbol] :=
          x^(2*n*FracPart[p])*(a+b*x^(-n)+c*x^(-2*n))^FracPart[p]/(c+b*x^n+a*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(m-2*n*p)*(d+e*x^n)^q*(c+b*x^n+a*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n] && EqQ[mn2,2*mn] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, mn_, c__, mn2_, p_, x_],
        optional: [m_, e__, n_, q_, a__, b__, mn_, c__, mn2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && eqq!(mn2_, Atom::num(2) * &mn_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let denominator = &c__ + &b__ * x_.pow(&n_) + &a__ * x_.pow(Atom::num(2) * &n_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ - Atom::num(2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * denominator.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(Atom::num(2) * &n_ * &frac_p) * (&a__ + &b__ * x_.pow(-&n_) + &c__ * x_.pow(Atom::num(-2) * &n_)).pow(&frac_p) / denominator.pow(frac_p), recursive)
        },
    ));
}

fn push_rules_rule_1898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1898,
        source: "Int[x_^m_.*(d_+e_.*x_^n_.)^q_.*(a_.+c_.*x_^mn2_.)^p_,x_Symbol] :=
          x^(2*n*FracPart[p])*(a+c*x^(-2*n))^FracPart[p]/(c+a*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(m-2*n*p)*(d+e*x^n)^q*(c+a*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[mn2,-2*n] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, d__, e__, n_, q_, a__, c__, mn2_, p_, x_],
        optional: [m_, e__, n_, q_, a__, c__, mn2_],
        when: {
            freeq!([a__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(mn2_, Atom::num(-2) * &n_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let denominator = &c__ + &a__ * x_.pow(Atom::num(2) * &n_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ - Atom::num(2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * denominator.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(Atom::num(2) * &n_ * &frac_p) * (&a__ + &c__ * x_.pow(Atom::num(-2) * &n_)).pow(&frac_p) / denominator.pow(frac_p), recursive)
        },
    ));
}

fn push_rules_rule_1899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, mn_, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1899,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^mn)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(mn_)).pow(q_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [f__, m_, d__, e__, mn_, q_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [e__, mn_, q_, a__, b__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&mn_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, m_, mn_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1900,
        source: "Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^mn)^q*(a+c*x^n2)^p,x] /;
        FreeQ[{a,c,d,e,f,m,mn,p,q},x] && EqQ[n2,-2*mn]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(mn_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_),
        with: [f__, m_, d__, e__, mn_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, mn_, q_, c__, n2_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, mn_, p_, q_], x_)
                && eqq!(n2_, Atom::num(-2) * &mn_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&d__ + &e__ * x_.pow(&mn_)).pow(&q_) * (&a__ + &c__ * x_.pow(&n2_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1901,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[mn,-n] && IntegerQ[p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, mn_, c__, p_, x_],
        optional: [m_, e__, q_, c__, p_, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1902,
        source: "Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, d__, e__, n_, q_, a__, b__, mn_, c__, p_, x_],
        optional: [m_, e__, q_, c__, p_, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let denominator = &b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ - &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * denominator.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&n_ * &frac_p) * (&a__ + &b__ / x_.pow(&n_) + &c__ * x_.pow(&n_)).pow(&frac_p) / denominator.pow(frac_p), recursive)
        },
    ));
}

fn push_rules_rule_1903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1903,
        source: "Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(d+e*x^n)^q*(a+b*x^(-n)+c*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[mn,-n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_),
        with: [f__, m_, d__, e__, n_, q_, a__, b__, mn_, c__, p_, x_],
        optional: [m_, e__, q_, c__, p_, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(-&n_) + &c__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(rubi_int_part(&m_)) * (&f__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, d2__, e1__, e2__, f__, m_, n_, n2_, non2_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 1904,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && EqQ[n2,2*n] && EqQ[non2,n/2] && EqQ[d2*e1+d1*e2,0] && (IntegerQ[q] || GtQ[d1,0] && GtQ[d2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, non2_, q_, d2__, e2__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [f__, m_, e1__, non2_, q_, e2__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
                && (integerq!(q_) || gtq!(d1__, 0) && gtq!(d2__, 0))
        },
        rhs: {
            let recursive_integrand = (&f__ * x_).pow(&m_)
                * (&d1__ * &d2__ + &e1__ * &e2__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, d2__, e1__, e2__, f__, m_, n_, n2_, non2_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 1905,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q] \\[Star]
            Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && EqQ[n2,2*n] && EqQ[non2,n/2] && EqQ[d2*e1+d1*e2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, non2_, q_, d2__, e2__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [f__, m_, e1__, non2_, q_, e2__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let denominator = &d1__ * &d2__ + &e1__ * &e2__ * x_.pow(&n_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = (&f__ * x_).pow(&m_)
                * denominator.pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&d1__ + &e1__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_q) * (&d2__ + &e2__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_q) / denominator.pow(frac_q), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negative_integer_binomial_power_skips_downvalue_1864() {
        let x = symbol!("x");
        let integrand = parse!("x*(1+x^3)^(-1)*(1+2*x^3+3*x^6)^(1/3)");
        let expansion_row = rubi_rules()
            .iter()
            .find(|rule| rule.downvalue_order == Some(1864))
            .expect("Rubi DownValue 1864 should be registered");
        let terminal_row = rubi_rules()
            .iter()
            .find(|rule| rule.downvalue_order == Some(1887))
            .expect("Rubi DownValue 1887 should be registered");

        assert!(
            matcher_rule(&integrand, x, expansion_row).is_none(),
            "DownValue 1864 requires IGtQ[q,0]"
        );
        assert!(
            matcher_rule(&integrand, x, terminal_row).is_some(),
            "negative q should fall through to Rubi's terminal DownValue 1887"
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
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
        / (d__ + e__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + c__ * x_.pow(n2_)).pow(p_) / (d__ + e__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d1__ + e1__ * x_.pow(non2_)).pow(q_)
        * (d2__ + e2__ * x_.pow(non2_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
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
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(n_))
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(n_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_)
        / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_) / (a__ + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(n_)) / (a__ + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (e__ * x_.pow(n_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (d__ + e__ * x_.pow(mn_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n2_ = symbols.n2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(mn_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let mn2_ = symbols.mn2_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (d__ + e__ * x_.pow(n_)).pow(q_)
        * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(mn2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (d__ + e__ * x_.pow(n_)).pow(q_)
        * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (d__ + e__ * x_.pow(n_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let mn2_ = symbols.mn2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(mn2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}
