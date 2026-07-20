// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 2 Exponentials. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_2_exponentials() {
    let samples = [
        // 2.1 u (F^(c (a+b x)))^n.input:12
        parse!("F^(c*(a+b*x))*(d+e*x)^m"),
        // 2.1 u (F^(c (a+b x)))^n.input:22
        parse!("F^(c*(a+b*x))/(d+e*x)^5"),
        // 2.1 u (F^(c (a+b x)))^n.input:28
        parse!("F^(c*(a+b*x))/(d^4+4*d^3*e*x+6*d^2*e^2*x^2+4*d*e^3*x^3+e^4*x^4)"),
        // 2.1 u (F^(c (a+b x)))^n.input:38
        parse!("F^(2+5*x)"),
        // 2.1 u (F^(c (a+b x)))^n.input:49
        parse!("F^(a+b*x)/x^(5/2)"),
        // 2.1 u (F^(c (a+b x)))^n.input:59
        parse!("F^(c*(a+b*x))/(d+e*x)^(7/2)"),
        // 2.1 u (F^(c (a+b x)))^n.input:70
        parse!("F^(c*(a+b*x))*(d+e*x+f*x^2+g*x^3)"),
        // 2.1 u (F^(c (a+b x)))^n.input:81
        parse!("exp(-a-b*x)*(a+b*x)^3/x^3"),
        // 2.1 u (F^(c (a+b x)))^n.input:91
        parse!("F^(a+b*(c+d*x))*(e+f*x)^2/x^4"),
        // 2.1 u (F^(c (a+b x)))^n.input:99
        parse!("exp(-a-b*x)*(a+b*x)^4/(c+d*x)"),
        // 2.1 u (F^(c (a+b x)))^n.input:111
        parse!("F^(c*(a+b*x))*log(d*x)^n*(e+e*n+e*(-1+b*c*x*log(F))*log(d*x))/x^2"),
        // 2.1 u (F^(c (a+b x)))^n.input:123
        parse!("(exp(a+b*x))^(1/2)/x^4"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:20
        parse!("x^3/(a+exp(c+d*x)*b)^2"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:41
        parse!("(a+b*(F^(g*(e+f*x)))^n)*(c+d*x)^2"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:50
        parse!("(a+b*(F^(g*(e+f*x)))^n)^2"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:60
        parse!("(a+b*(F^(g*(e+f*x)))^n)^3/(c+d*x)^3"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:72
        parse!("1/(a+b*(F^(g*(e+f*x)))^n)^2"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:85
        parse!("(a+exp(x)*b)*(c+d*x)^(1/2)"),
        // 2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.input:115
        parse!("F^(c+d*x)*x/(a+b*F^(c+d*x))^2"),
        // 2.3 Exponential functions.input:12
        parse!("exp(d*x)/(a+exp(c+d*x)*b)"),
        // 2.3 Exponential functions.input:22
        parse!("F^(c+d*x)*(a+b*F^(c+d*x))^n"),
        // 2.3 Exponential functions.input:36
        parse!("exp(4*x)/(a+exp(2*x)*b)^2"),
        // 2.3 Exponential functions.input:45
        parse!("1/(exp(n*x)*(a+exp(n*x)*b)^3)"),
        // 2.3 Exponential functions.input:52
        parse!("exp(x)/(1-exp(2*x))"),
        // 2.3 Exponential functions.input:62
        parse!("f^x*x^2/(a+b*f^(2*x))^2"),
        // 2.3 Exponential functions.input:73
        parse!("1/(b/f^x+a*f^x)^2"),
        // 2.3 Exponential functions.input:82
        parse!("f^(a+b*x+c*x^2)*g^(d+e*x+f*x^2)"),
        // 2.3 Exponential functions.input:95
        parse!("f^(a+b*x^2)*x^3"),
        // 2.3 Exponential functions.input:105
        parse!("f^(a+b*x^2)*x^8"),
        // 2.3 Exponential functions.input:115
        parse!("f^(a+b*x^2)/x^12"),
        // 2.3 Exponential functions.input:121
        parse!("f^(a+b*x^3)*x^5"),
        // 2.3 Exponential functions.input:131
        parse!("f^(a+b*x^3)*x"),
        // 2.3 Exponential functions.input:143
        parse!("f^(a+b/x)"),
        // 2.3 Exponential functions.input:149
        parse!("f^(a+b/x)/x^6"),
        // 2.3 Exponential functions.input:159
        parse!("f^(a+b/x^2)/x^5"),
        // 2.3 Exponential functions.input:168
        parse!("f^(a+b/x^2)*x^2"),
        // 2.3 Exponential functions.input:175
        parse!("f^(a+b/x^2)/x^12"),
        // 2.3 Exponential functions.input:184
        parse!("f^(a+b/x^3)/x^4"),
        // 2.3 Exponential functions.input:194
        parse!("f^(a+b/x^3)/x^2"),
        // 2.3 Exponential functions.input:206
        parse!("f^(a+b*x^n)/x^3"),
        // 2.3 Exponential functions.input:212
        parse!("f^(a+b*x^n)*x^(-1-n)"),
        // 2.3 Exponential functions.input:228
        parse!("f^(c*(a+b*x)^2)*x"),
        // 2.3 Exponential functions.input:252
        parse!("f^(c/(a+b*x))*x"),
        // 2.3 Exponential functions.input:259
        parse!("f^(c/(a+b*x)^2)*x^2"),
        // 2.3 Exponential functions.input:277
        parse!("f^(c*(a+b*x))*x^m"),
        // 2.3 Exponential functions.input:299
        parse!("F^(a+b*(c+d*x)^2)*(c+d*x)^5"),
        // 2.3 Exponential functions.input:309
        parse!("F^(a+b*(c+d*x)^2)*(c+d*x)^10"),
        // 2.3 Exponential functions.input:315
        parse!("F^(a+b*(c+d*x)^2)/(c+d*x)^2"),
        // 2.3 Exponential functions.input:325
        parse!("F^(a+b*(c+d*x)^3)*(c+d*x)^8"),
        // 2.3 Exponential functions.input:335
        parse!("F^(a+b*(c+d*x)^3)*(c+d*x)"),
        // 2.3 Exponential functions.input:341
        parse!("f^(a+b*(c+d*x)^(1/3))"),
        // 2.3 Exponential functions.input:353
        parse!("F^(a+b/(c+d*x))/(c+d*x)^4"),
        // 2.3 Exponential functions.input:362
        parse!("F^(a+b/(c+d*x)^2)*(c+d*x)"),
        // 2.3 Exponential functions.input:369
        parse!("F^(a+b/(c+d*x)^2)/(c+d*x)^13"),
        // 2.3 Exponential functions.input:379
        parse!("F^(a+b/(c+d*x)^2)/(c+d*x)^8"),
        // 2.3 Exponential functions.input:388
        parse!("F^(a+b/(c+d*x)^3)*(c+d*x)^2"),
        // 2.3 Exponential functions.input:398
        parse!("F^(a+b/(c+d*x)^3)"),
        // 2.3 Exponential functions.input:406
        parse!("F^(a+b*(c+d*x)^n)*(c+d*x)^2"),
        // 2.3 Exponential functions.input:416
        parse!("F^(a+b*(c+d*x)^n)*(c+d*x)^(-1+3*n)"),
        // 2.3 Exponential functions.input:426
        parse!("(a+b*x)^(-1+1/2*n)/F^(c*(a+b*x)^n)"),
        // 2.3 Exponential functions.input:436
        parse!("F^(a+b*(c+d*x)^2)"),
        // 2.3 Exponential functions.input:451
        parse!("F^(a+b/(c+d*x))/(e+f*x)^4"),
        // 2.3 Exponential functions.input:461
        parse!("exp(e/(c+d*x)^2)*(a+b*x)^2"),
        // 2.3 Exponential functions.input:476
        parse!("F^(e+f*(a+b*x)/(c+d*x))/(g+h*x)^2"),
        // 2.3 Exponential functions.input:484
        parse!("f^(a+b*x+c*x^2)"),
        // 2.3 Exponential functions.input:494
        parse!("exp((a+b*x)*(c+d*x))*x^2"),
        // 2.3 Exponential functions.input:512
        parse!("f^(a+b*x+c*x^2)/(b+2*c*x)^3"),
        // 2.3 Exponential functions.input:518
        parse!("f^(b*x+c*x^2)/(b+2*c*x)^3"),
        // 2.3 Exponential functions.input:530
        parse!("exp(d+e*x)*x^2/(a+b*x+c*x^2)"),
        // 2.3 Exponential functions.input:542
        parse!("2^x/(a+4^x*b)"),
        // 2.3 Exponential functions.input:548
        parse!("2^x/(a-b/4^x)"),
        // 2.3 Exponential functions.input:562
        parse!("4^x/(a+2^x*b)^(1/2)"),
        // 2.3 Exponential functions.input:573
        parse!("1/(2+3*exp(x)+exp(2*x))"),
        // 2.3 Exponential functions.input:583
        parse!("x^2/(2+3*exp(x)+exp(2*x))"),
        // 2.3 Exponential functions.input:590
        parse!("x/(1+2*f^(c+d*x)+f^(2*c+2*d*x))"),
        // 2.3 Exponential functions.input:599
        parse!("1/(2+f^(-c-d*x)+f^(c+d*x))"),
        // 2.3 Exponential functions.input:609
        parse!("x^2/(a+b*f^(-c-d*x)+c*f^(c+d*x))"),
        // 2.3 Exponential functions.input:621
        parse!("(a+b*F^(c*(d+e*x)^(1/2)/(d*f-e*f*x)^(1/2)))^2/(d^2-e^2*x^2)"),
        // 2.3 Exponential functions.input:635
        parse!("a^x*b^x*x"),
        // 2.3 Exponential functions.input:647
        parse!("(d+exp(h+i*x)*e)*(f+g*x)/(a+exp(h+i*x)*b+exp(2*h+2*i*x)*c)"),
        // 2.3 Exponential functions.input:666
        parse!("F^(f*(a+b*log(c*(d+e*x)^n)^2))*(d*g+e*g*x)^m"),
        // 2.3 Exponential functions.input:672
        parse!("F^(f*(a+b*log(c*(d+e*x)^n)^2))/(d*g+e*g*x)^3"),
        // 2.3 Exponential functions.input:691
        parse!("F^(f*(a+b*log(c*(d+e*x)^n))^2)/(d*g+e*g*x)"),
        // 2.3 Exponential functions.input:708
        parse!("exp(a+b*x+c*x^2)*(b+2*c*x)*(a+b*x+c*x^2)^m"),
        // 2.3 Exponential functions.input:715
        parse!("exp(a+b*x+c*x^2)*(b+2*c*x)/(a+b*x+c*x^2)^3"),
        // 2.3 Exponential functions.input:724
        parse!("exp(a+b*x+c*x^2)*(b+2*c*x)/(a+b*x+c*x^2)^(9/2)"),
        // 2.3 Exponential functions.input:740
        parse!("exp(2-x^2)*x"),
        // 2.3 Exponential functions.input:752
        parse!("((-1)/exp(x)+exp(x))/(1/exp(x)+exp(x))"),
        // 2.3 Exponential functions.input:758
        parse!("exp(x)*(1+exp(2*x))^(1/2)"),
        // 2.3 Exponential functions.input:772
        parse!("exp(x)^(1/2)/(x)^(1/2)"),
        // 2.3 Exponential functions.input:786
        parse!("exp(x)*sech(exp(x))"),
        // 2.3 Exponential functions.input:794
        parse!("exp(2*x)/(1+exp(x))^(1/3)"),
        // 2.3 Exponential functions.input:814
        parse!("(a+exp(x)*b)^4"),
        // 2.3 Exponential functions.input:823
        parse!("exp(x)/(-1-8*exp(x)+exp(2*x))"),
        // 2.3 Exponential functions.input:830
        parse!("exp(x^2)*x*(1-exp(2*x^2))^(1/2)"),
        // 2.3 Exponential functions.input:839
        parse!("exp(x)*((-1)/exp(x)+exp(x))^2"),
        // 2.3 Exponential functions.input:851
        parse!("(1+exp(x))/(exp(x)+x)^(1/2)"),
        // 2.3 Exponential functions.input:861
        parse!("k^(1/2*x)+x^(k)^(1/2)"),
        // 2.3 Exponential functions.input:876
        parse!("(5*x+exp(x)*(3+2*x))/(exp(x)+x)^(1/3)"),
        // 2.3 Exponential functions.input:901
        parse!("(5*x^2+3*(exp(x)+x)^(1/3)+exp(x)*(3*x+2*x^2))/(x*(exp(x)+x)^(1/3))"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
