// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 8 Special functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_8_special() {
    let x = symbol!("x");
    let samples = [
        // 8.1 Error functions.input:10
        parse!("x^5*erf(b*x)"),
        // 8.1 Error functions.input:23
        parse!("erf(b*x)/x^6"),
        // 8.1 Error functions.input:78
        parse!("exp(c+d*x^2)*x^5*erf(b*x)"),
        // 8.1 Error functions.input:98
        parse!("exp(c+b^2*x^2)*erf(b*x)/x^2"),
        // 8.1 Error functions.input:139
        parse!("x^5*symbolica_integrate::erfc(b*x)"),
        // 8.1 Error functions.input:152
        parse!("symbolica_integrate::erfc(b*x)/x^6"),
        // 8.1 Error functions.input:200
        parse!("exp(c-b^2*x^2)*symbolica_integrate::erfc(b*x)"),
        // 8.1 Error functions.input:221
        parse!("exp(c+b^2*x^2)*symbolica_integrate::erfc(b*x)/x"),
        // 8.1 Error functions.input:235
        parse!("x^4*symbolica_integrate::erfc(b*x)/exp(b^2*x^2)"),
        // 8.1 Error functions.input:270
        parse!("x*symbolica_integrate::erfi(b*x)"),
        // 8.1 Error functions.input:286
        parse!("(c+d*x)*symbolica_integrate::erfi(a+b*x)"),
        // 8.1 Error functions.input:311
        parse!("(c+d*x)*symbolica_integrate::erfi(a+b*x)^2"),
        // 8.1 Error functions.input:329
        parse!("exp(c+b^2*x^2)*symbolica_integrate::erfi(b*x)"),
        // 8.1 Error functions.input:370
        parse!("exp(c+b^2*x^2)*symbolica_integrate::erfi(b*x)/x^4"),
        // 8.10 Formal derivatives.input:6
        parse!("der(1,f,x)"),
        // 8.10 Formal derivatives.input:26
        parse!("(a+b*der(1,f,x))^n*der(2,f,x)"),
        // 8.10 Formal derivatives.input:40
        parse!("(g(x)*der(1,f,x)+f(x)*der(1,g,x))/(a+b*f(x)*g(x))"),
        // 8.10 Formal derivatives.input:73
        parse!("cos(f(x)*g(x))*(g(x)*der(1,f,x)+f(x)*der(1,g,x))"),
        // 8.10 Formal derivatives.input:92
        parse!("der(1,F,g(x)*der(m,f,x)^2)*der(m,f,x)*(der(1,g,x)*der(m,f,x)+2*g(x)*der(1+m,f,x))"),
        // 8.2 Fresnel integral functions.input:11
        parse!("x^6*symbolica_integrate::fresnel_s(b*x)"),
        // 8.2 Fresnel integral functions.input:50
        parse!("x^3*symbolica_integrate::fresnel_s(b*x)^2"),
        // 8.2 Fresnel integral functions.input:66
        parse!("(c+d*x)^2*symbolica_integrate::fresnel_s(a+b*x)^2"),
        // 8.2 Fresnel integral functions.input:95
        parse!("sin(1/2*pi*b^2*x^2)/symbolica_integrate::fresnel_s(b*x)^2"),
        // 8.2 Fresnel integral functions.input:131
        parse!("x^5*cos(1/2*pi*b^2*x^2)*symbolica_integrate::fresnel_s(b*x)"),
        // 8.2 Fresnel integral functions.input:158
        parse!("x^4*symbolica_integrate::fresnel_c(b*x)"),
        // 8.2 Fresnel integral functions.input:191
        parse!("x^7*symbolica_integrate::fresnel_c(b*x)^2"),
        // 8.2 Fresnel integral functions.input:203
        parse!("symbolica_integrate::fresnel_c(b*x)^2/x^5"),
        // 8.2 Fresnel integral functions.input:233
        parse!("symbolica_integrate::fresnel_c(b*x)*sin(c+1/2*pi*b^2*x^2)"),
        // 8.2 Fresnel integral functions.input:250
        parse!("x^3*cos(1/2*pi*b^2*x^2)*symbolica_integrate::fresnel_c(b*x)"),
        // 8.3 Exponential integral functions.input:17
        parse!("symbolica_integrate::exp_integral_e(1,b*x)/x^3"),
        // 8.3 Exponential integral functions.input:31
        parse!("symbolica_integrate::exp_integral_e(3,b*x)/x^2"),
        // 8.3 Exponential integral functions.input:45
        parse!("x^4*symbolica_integrate::exp_integral_e(-2,b*x)"),
        // 8.3 Exponential integral functions.input:64
        parse!("x*symbolica_integrate::exp_integral_e(-1,b*x)"),
        // 8.3 Exponential integral functions.input:82
        parse!("symbolica_integrate::exp_integral_e(n,x)/x^n"),
        // 8.3 Exponential integral functions.input:107
        parse!("(c+d*x)^2*symbolica_integrate::exp_integral_e(2,a+b*x)"),
        // 8.3 Exponential integral functions.input:121
        parse!("symbolica_integrate::exp_integral_e(3,a+b*x)/(c+d*x)^4"),
        // 8.3 Exponential integral functions.input:142
        parse!("(c+d*x)^2*symbolica_integrate::exp_integral_e(-3,a+b*x)"),
        // 8.3 Exponential integral functions.input:172
        parse!("x*symbolica_integrate::exp_integral_ei(b*x)"),
        // 8.3 Exponential integral functions.input:209
        parse!("symbolica_integrate::exp_integral_ei(a+b*x)^2"),
        // 8.3 Exponential integral functions.input:241
        parse!("exp(b*x)*symbolica_integrate::exp_integral_ei(b*x)/x^3"),
        // 8.3 Exponential integral functions.input:266
        parse!("symbolica_integrate::log_integral(b*x)/x^3"),
        // 8.4 Trig integral functions.input:22
        parse!("symbolica_integrate::sin_integral(b*x)^2"),
        // 8.4 Trig integral functions.input:37
        parse!("x^2*symbolica_integrate::sin_integral(a+b*x)^2"),
        // 8.4 Trig integral functions.input:83
        parse!("x*cos(a+b*x)*symbolica_integrate::sin_integral(a+b*x)"),
        // 8.4 Trig integral functions.input:112
        parse!("x^2*symbolica_integrate::cos_integral(b*x)^2"),
        // 8.4 Trig integral functions.input:149
        parse!("symbolica_integrate::cos_integral(b*x)*sin(b*x)"),
        // 8.4 Trig integral functions.input:169
        parse!("x*symbolica_integrate::cos_integral(a+b*x)*sin(a+b*x)"),
        // 8.5 Hyperbolic integral functions.input:16
        parse!("symbolica_integrate::sinh_integral(b*x)/x^2"),
        // 8.5 Hyperbolic integral functions.input:48
        parse!("symbolica_integrate::sinh_integral(d*(a+b*log(c*x^n)))/x"),
        // 8.5 Hyperbolic integral functions.input:71
        parse!("cosh(5*x)*symbolica_integrate::sinh_integral(2*x)"),
        // 8.5 Hyperbolic integral functions.input:107
        parse!("symbolica_integrate::cosh_integral(b*x)/x"),
        // 8.5 Hyperbolic integral functions.input:142
        parse!("symbolica_integrate::cosh_integral(d*(a+b*log(c*x^n)))/x^3"),
        // 8.5 Hyperbolic integral functions.input:169
        parse!("x*symbolica_integrate::cosh_integral(a+b*x)*sinh(a+b*x)"),
        // 8.6 Gamma functions.input:13
        parse!("x^2*symbolica_integrate::rubi_gamma(0,a*x)"),
        // 8.6 Gamma functions.input:27
        parse!("symbolica_integrate::rubi_gamma(1,a*x)/x^4"),
        // 8.6 Gamma functions.input:48
        parse!("x^2*symbolica_integrate::rubi_gamma(-1,a*x)"),
        // 8.6 Gamma functions.input:60
        parse!("symbolica_integrate::rubi_gamma(-2,a*x)/x"),
        // 8.6 Gamma functions.input:83
        parse!("symbolica_integrate::rubi_gamma(1/2,a*x)/x^3"),
        // 8.6 Gamma functions.input:99
        parse!("(d*x)^m*symbolica_integrate::rubi_gamma(-1,b*x)"),
        // 8.6 Gamma functions.input:121
        parse!("symbolica_integrate::rubi_gamma(n,2*x)/x^3"),
        // 8.6 Gamma functions.input:140
        parse!("(c+d*x)*symbolica_integrate::rubi_gamma(1,a+b*x)"),
        // 8.6 Gamma functions.input:152
        parse!("symbolica_integrate::rubi_gamma(2,a+b*x)/(c+d*x)^3"),
        // 8.6 Gamma functions.input:173
        parse!("symbolica_integrate::rubi_gamma(-1,a+b*x)/(c+d*x)^4"),
        // 8.6 Gamma functions.input:187
        parse!("symbolica_integrate::rubi_gamma(-3,a+b*x)/(c+d*x)^2"),
        // 8.6 Gamma functions.input:236
        parse!("(c+d*x)*symbolica_integrate::rubi_gamma(n,a+b*x)"),
        // 8.6 Gamma functions.input:254
        parse!("(c+d*x)*symbolica_integrate::log_gamma(a+b*x)"),
        // 8.8 Polylogarithm function.input:14
        parse!("x^2*polylog(2,a*x)"),
        // 8.8 Polylogarithm function.input:27
        parse!("polylog(3,a*x)/x^2"),
        // 8.8 Polylogarithm function.input:49
        parse!("polylog(3,a*x^2)/x^3"),
        // 8.8 Polylogarithm function.input:63
        parse!("polylog(2,a*x^q)/x"),
        // 8.8 Polylogarithm function.input:80
        parse!("polylog(2,a*x)/(d*x)^(1/2)"),
        // 8.8 Polylogarithm function.input:102
        parse!("polylog(3,a*x^2)/(d*x)^(1/2)"),
        // 8.8 Polylogarithm function.input:117
        parse!("polylog(3,a*x^q)/(d*x)^(3/2)"),
        // 8.8 Polylogarithm function.input:166
        parse!("polylog(3,c*(a+b*x))"),
        // 8.8 Polylogarithm function.input:182
        parse!("polylog(2,x)/(-1+x)"),
        // 8.8 Polylogarithm function.input:210
        parse!("log(1-c*x)*polylog(2,c*x)/x"),
        // 8.8 Polylogarithm function.input:227
        parse!("x*(g+h*log(f*(d+e*x)^n))*polylog(2,c*(a+b*x))"),
        // 8.8 Polylogarithm function.input:245
        parse!("x*(a+b*x+c*x^2)*log(1-d*x)*polylog(2,d*x)"),
        // 8.9 Product logarithm function.input:22
        parse!("1/(c*symbolica_integrate::product_log(a+b*x))^(1/2)"),
        // 8.9 Product logarithm function.input:38
        parse!("x*symbolica_integrate::product_log(a+b*x)"),
        // 8.9 Product logarithm function.input:63
        parse!("(c*symbolica_integrate::product_log(a+b*x))^(1/2)"),
        // 8.9 Product logarithm function.input:83
        parse!("symbolica_integrate::product_log(a*x)/x^2"),
        // 8.9 Product logarithm function.input:103
        parse!("symbolica_integrate::product_log(a*x)^3/x^3"),
        // 8.9 Product logarithm function.input:114
        parse!("1/(x*symbolica_integrate::product_log(a*x))"),
        // 8.9 Product logarithm function.input:128
        parse!("x^5/symbolica_integrate::product_log(a*x)^3"),
        // 8.9 Product logarithm function.input:147
        parse!("x^4/(c*symbolica_integrate::product_log(a*x))^(1/2)"),
        // 8.9 Product logarithm function.input:161
        parse!("(c*symbolica_integrate::product_log(a*x))^p/x^3"),
        // 8.9 Product logarithm function.input:208
        parse!("x^5/symbolica_integrate::product_log(a*x^2)"),
        // 8.9 Product logarithm function.input:227
        parse!("1/(x*symbolica_integrate::product_log(a*x^2)^2)"),
        // 8.9 Product logarithm function.input:253
        parse!("1/(x*(c*symbolica_integrate::product_log(a*x^2))^(1/2))"),
        // 8.9 Product logarithm function.input:268
        parse!("x^3*symbolica_integrate::product_log(a/x)"),
        // 8.9 Product logarithm function.input:288
        parse!("x^2*(symbolica_integrate::product_log(a/x))^(1/2)"),
        // 8.9 Product logarithm function.input:302
        parse!("1/(x^4*(symbolica_integrate::product_log(a/x))^(1/2))"),
        // 8.9 Product logarithm function.input:317
        parse!("symbolica_integrate::product_log(a/x^(1/5))^4"),
        // 8.9 Product logarithm function.input:339
        parse!("x^(-1-2*n)*(c*symbolica_integrate::product_log(a*x^n))^(7/2)"),
        // 8.9 Product logarithm function.input:350
        parse!("x^(-1+n)/(c*symbolica_integrate::product_log(a*x^n))^(5/2)"),
        // 8.9 Product logarithm function.input:370
        parse!("x^(-1+n*(2-p))*(c*symbolica_integrate::product_log(a*x^n))^p"),
        // 8.9 Product logarithm function.input:386
        parse!("1/(x*(1+symbolica_integrate::product_log(a*x^2)))"),
        // 8.9 Product logarithm function.input:413
        parse!(
            "symbolica_integrate::product_log(a/(x)^(1/2))^3/(1+symbolica_integrate::product_log(a/(x)^(1/2)))"
        ),
        // 8.9 Product logarithm function.input:427
        parse!(
            "symbolica_integrate::product_log(a*x^(1/(1-p)))^p/(1+symbolica_integrate::product_log(a*x^(1/(1-p))))"
        ),
    ];
    assert_eq!(samples.len(), 100);
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
