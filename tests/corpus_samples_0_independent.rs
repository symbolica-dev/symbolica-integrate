// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 0 Independent test suites. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_0_independent() {
    let samples = [
        // Apostol Problems.input:10
        parse!("(1+2*x)^(1/2)"),
        // Apostol Problems.input:30
        parse!("x/(1+x^2+(1+x^2)^(3/2))^(1/2)"),
        // Apostol Problems.input:59
        parse!("cos(x)^4"),
        // Apostol Problems.input:90
        parse!("log(x)^2"),
        // Apostol Problems.input:127
        parse!("exp(x)*x^2"),
        // Apostol Problems.input:154
        parse!("atan((x)^(1/2))"),
        // Apostol Problems.input:195
        parse!("x/(4-x^2+(4-x^2)^(1/2))"),
        // Apostol Problems.input:220
        parse!("(1+x^4)/(x*(1+x^2)^2)"),
        // Apostol Problems.input:243
        parse!("(5+x^2)^(1/2)"),
        // Apostol Problems.input:278
        parse!("1/log(x)^2"),
        // Bondarenko Problems.input:24
        parse!("(1+(x)^(1/2)+(1+2*x+2*(x)^(1/2))^(1/2))^(1/2)"),
        // Bondarenko Problems.input:43
        parse!("atan(x)*log(x)/x"),
        // Charlwood Problems.input:17
        parse!("log(1+x*(1+x^2)^(1/2))"),
        // Charlwood Problems.input:74
        parse!("x*atan(x)*log(x+(1+x^2)^(1/2))/(1+x^2)^(1/2)"),
        // Charlwood Problems.input:131
        parse!("sec(x)/(-1+sec(x)^4)^(1/2)"),
        // Hearn Problems.input:17
        parse!("1/(3-2*x+x^2)"),
        // Hearn Problems.input:40
        parse!("1/(x^2*(a+b*x))"),
        // Hearn Problems.input:63
        parse!("1/(2+x^6)"),
        // Hearn Problems.input:84
        parse!("log(x)/(b+a*x)^2"),
        // Hearn Problems.input:113
        parse!("x*sin(x)^2"),
        // Hearn Problems.input:132
        parse!("sin(a+b*x)^2"),
        // Hearn Problems.input:151
        parse!("cos(x)^2*sin(x)^2"),
        // Hearn Problems.input:181
        parse!("exp(2*x+a*x)"),
        // Hearn Problems.input:212
        parse!("x/(a+b*x)^(1/2)"),
        // Hearn Problems.input:235
        parse!("10/(-4+x^2)^(1/2)+1/(-1+x^2)^(1/2)"),
        // Hearn Problems.input:254
        parse!("1/(x*(-alpha^2+2*h*x^2-2*k*x^4)^(1/2))"),
        // Hearn Problems.input:281
        parse!("x*log(a+x^2)"),
        // Hearn Problems.input:300
        parse!("x*log(x+(1+x^2)^(1/2))"),
        // Hearn Problems.input:323
        parse!("1/(10-12*x+9*x^2)"),
        // Jeffrey Problems.input:20
        parse!("(-1+4*cos(x)+5*cos(x)^2)/(-1-4*cos(x)-3*cos(x)^2+4*cos(x)^3)"),
        // Moses Problems.input:26
        parse!("2*exp(x)+exp(2*x)+x^2"),
        // Moses Problems.input:53
        parse!("x*(1+x)^(1/2)"),
        // Moses Problems.input:84
        parse!("x^2*asin(x)"),
        // Moses Problems.input:115
        parse!("-B*(A^2+B^2)/((1+x^2)*(B^2-A^2*x^2))"),
        // Moses Problems.input:140
        parse!("cos(x)*sin(x)^2"),
        // Moses Problems.input:161
        parse!("r/(-a^2-e^2+2*euler_e*r^2)^(1/2)"),
        // Stewart Problems.input:23
        parse!("log(x)"),
        // Stewart Problems.input:42
        parse!("x*cosh(a*x)"),
        // Stewart Problems.input:61
        parse!("exp(x^2)*x^5"),
        // Stewart Problems.input:82
        parse!("cos(x)^4*sin(x)^4"),
        // Stewart Problems.input:100
        parse!("tan(x)^6"),
        // Stewart Problems.input:119
        parse!("cos(x)^5*sin(x)"),
        // Stewart Problems.input:140
        parse!("x^3/(4+x^2)^(1/2)"),
        // Stewart Problems.input:159
        parse!("1/(2+2*x+x^2)^2"),
        // Stewart Problems.input:180
        parse!("(1-x-x^2+x^3+x^4)/(-x+x^3)"),
        // Stewart Problems.input:199
        parse!("(-3+5*x+6*x^2)/(-3*x+2*x^2+x^3)"),
        // Stewart Problems.input:218
        parse!("(-1-2*x+x^2)/((-1+x)^2*(1+x^2))"),
        // Stewart Problems.input:239
        parse!("(x)^(1/2)/(1+x)"),
        // Stewart Problems.input:258
        parse!("1/(3-5*sin(x))"),
        // Stewart Problems.input:279
        parse!("cos(x)^2*sin(x)^2"),
        // Stewart Problems.input:298
        parse!("exp(2*x)/(1+exp(x))"),
        // Stewart Problems.input:317
        parse!("x^5*cosh(x)"),
        // Stewart Problems.input:336
        parse!("(x)^(1/2)/(1+x^(1/3))"),
        // Stewart Problems.input:357
        parse!("x^2/(5-4*x^2)^(1/2)"),
        // Stewart Problems.input:375
        parse!("sin(2*x)^6"),
        // Stewart Problems.input:394
        parse!("tan(x)^3"),
        // Timofeev Problems.input:31
        parse!("1/(4-cos(x)^2)"),
        // Timofeev Problems.input:58
        parse!("cot(3/4*x)^2"),
        // Timofeev Problems.input:85
        parse!("1/(x-x^2)^(1/2)"),
        // Timofeev Problems.input:112
        parse!("cos(x)^4*sin(x)^2"),
        // Timofeev Problems.input:141
        parse!("x^2/(5+2*x+x^2)"),
        // Timofeev Problems.input:170
        parse!("1/(1+x^2+x^4)"),
        // Timofeev Problems.input:193
        parse!("1/(x^4*(a^4-x^4))"),
        // Timofeev Problems.input:216
        parse!("1/(-1+x^3)^2"),
        // Timofeev Problems.input:243
        parse!("x^3/(a^4+x^4)^3"),
        // Timofeev Problems.input:272
        parse!("(b1+c1*x)*(a+2*b*x+c*x^2)^3"),
        // Timofeev Problems.input:299
        parse!("1/(1+(1+x)^(1/2))"),
        // Timofeev Problems.input:323
        parse!("((-1+x)^2*(1+x))^(1/3)/x^2"),
        // Timofeev Problems.input:348
        parse!("(1+2*x)/((4+4*x+3*x^2)*(-1+6*x+x^2)^(1/2))"),
        // Timofeev Problems.input:371
        parse!("1/(1+x+x^2)^(1/2)"),
        // Timofeev Problems.input:394
        parse!("1/(1+8*x+3*x^2)^(5/2)"),
        // Timofeev Problems.input:419
        parse!("x^2*(3+4*x^4)^(5/4)"),
        // Timofeev Problems.input:442
        parse!("(-1+x^2)/(x*(1+x^4)^(1/2))"),
        // Timofeev Problems.input:471
        parse!("1/tan(x)^5"),
        // Timofeev Problems.input:494
        parse!("cot(x)^4*csc(x)^3"),
        // Timofeev Problems.input:511
        parse!("sin(4*x)/sin(x)^4"),
        // Timofeev Problems.input:536
        parse!("(1-sin(2*x))^(1/2)"),
        // Timofeev Problems.input:559
        parse!("1/(sin(x)*sin(2*x)^(3/2))"),
        // Timofeev Problems.input:586
        parse!("sin(x)/cos(2*x)^(5/2)"),
        // Timofeev Problems.input:611
        parse!("cot(x)*sin(x)^9/(2-5*sin(x)^3)^(4/3)"),
        // Timofeev Problems.input:638
        parse!("1/(-1-2*x+x^2)^(5/2)"),
        // Timofeev Problems.input:665
        parse!("x*sin(x)^3/cos(x)^4"),
        // Timofeev Problems.input:690
        parse!("a^(k*x)-a^(l*x)"),
        // Timofeev Problems.input:713
        parse!("(exp(x)+exp(5*x))/(-1+exp(x)-exp(2*x)+exp(3*x))"),
        // Timofeev Problems.input:738
        parse!("exp(m*x)*sin(x)^3"),
        // Timofeev Problems.input:760
        parse!("exp(x)*(1-cos(x))/(1+sin(x))"),
        // Timofeev Problems.input:787
        parse!("sech(x)^(3/4)*tanh(x)^5"),
        // Timofeev Problems.input:814
        parse!("1/(exp(2*x)*cosh(x)^4)"),
        // Timofeev Problems.input:841
        parse!("1/(x*(a+b*log(x)))"),
        // Timofeev Problems.input:864
        parse!("((-1)/exp(x)+exp(x))*log(1+exp(2*x))"),
        // Timofeev Problems.input:889
        parse!("(1-x^2)^(3/2)*asin(x)/x^6"),
        // Timofeev Problems.input:914
        parse!("(1+x^2)*atan(x)/x^5"),
        // Timofeev Problems.input:941
        parse!("atan(((-a+x)/(a+x))^(1/2))"),
        // Welz Problems.input:43
        parse!("((x)^(1/2)-(-1+x^2)^(1/2))^2/((1+x-x^2)^2*(-1+x^2)^(1/2))"),
        // Welz Problems.input:78
        parse!("x^3*log(2+x)^3*log(3+x)"),
        // Welz Problems.input:101
        parse!("1/((3-2*x)^(21/2)*(1+x+2*x^2)^10)"),
        // Welz Problems.input:137
        parse!("(1+p*x^2+x^4)^(1/2)/(1-x^4)"),
        // Welz Problems.input:173
        parse!("x/((10+x^3+6*(3)^(1/2))*(1+x^3)^(1/2))"),
        // Welz Problems.input:208
        parse!("(1-x)^2/(1-x^3)^(4/3)"),
        // Wester Problems.input:37
        parse!("1/2*log((-a^2+x^2)^2)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
