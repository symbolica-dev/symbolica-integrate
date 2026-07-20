// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 6 Hyperbolic functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_6_hyperbolic() {
    let samples = [
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:12
        parse!("(c+d*x)^4*sinh(a+b*x)"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:93
        parse!("x/sinh(x)^(3/2)-x*(sinh(x))^(1/2)"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:164
        parse!("x^3*(a+1i*a*sinh(e+f*x))^(1/2)"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:282
        parse!("(e+f*x)*csch(c+d*x)/(a+1i*a*sinh(c+d*x))"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:352
        parse!("(e+f*x)^3*cosh(c+d*x)^2/(a+1i*a*sinh(c+d*x))"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:435
        parse!("(e+f*x)^3*cosh(c+d*x)/(a+b*sinh(c+d*x))^2"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:536
        parse!("cosh(c+d*x)^2*sinh(c+d*x)^3/(a+b*sinh(c+d*x))"),
        // 6.1 Hyperbolic sine/6.1.1 (c+d x)^m (a+b sinh)^n.input:605
        parse!("(e+f*x)^2*coth(c+d*x)*csch(c+d*x)/(a+b*sinh(c+d*x))"),
        // 6.1 Hyperbolic sine/6.1.3 (e x)^m (a+b sinh(c+d x^n))^p.input:27
        parse!("x^2*sinh(a+b*x^2)^3"),
        // 6.1 Hyperbolic sine/6.1.3 (e x)^m (a+b sinh(c+d x^n))^p.input:120
        parse!("sinh(a+b*x^n)^2/x"),
        // 6.1 Hyperbolic sine/6.1.4 (d+e x)^m sinh(a+b x+c x^2)^n.input:26
        parse!("x*sinh(a+b*x+c*x^2)^2"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:53
        parse!("1/(b*sinh(c+d*x))^(4/3)"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:118
        parse!("csch(x)^4/(a+b*sinh(x))^2"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:161
        parse!("(A+B*sinh(x))/(a+1i*a*sinh(x))^(3/2)"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:234
        parse!("cosh(x)^2/(1i+sinh(x))^2"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:292
        parse!("coth(x)^6/(1i+sinh(x))^2"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:374
        parse!("sinh(a+b*log(c*x^n))^(5/2)/x"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:437
        parse!("exp(c*(a+b*x))*(sinh(a*c+b*c*x)^2)^(3/2)"),
        // 6.1 Hyperbolic sine/6.1.5 Hyperbolic sine functions.input:478
        parse!("(x+sinh(x))^3"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:62
        parse!("csch(c+d*x)^3/(a+b*sinh(c+d*x)^2)^2"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:120
        parse!("csch(e+f*x)^3/(a+b*sinh(e+f*x)^2)^(1/2)"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:180
        parse!("(a+b*sinh(c+d*x)^3)^2"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:241
        parse!("csch(c+d*x)^5*(a+b*sinh(c+d*x)^4)^2"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:280
        parse!("sinh(c+d*x)^9/(a-b*sinh(c+d*x)^4)^2"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:349
        parse!("sech(c+d*x)^6*(a+b*sinh(c+d*x)^2)"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:403
        parse!("cosh(c+d*x)/(a+b*sinh(c+d*x)^2)^3"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:461
        parse!("cosh(e+f*x)^4/(a+b*sinh(e+f*x)^2)^(5/2)"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:536
        parse!("tanh(e+f*x)^5/(a+a*sinh(e+f*x)^2)^(3/2)"),
        // 6.1 Hyperbolic sine/6.1.7 hyper^m (a+b sinh^n)^p.input:571
        parse!("coth(e+f*x)^4*(a+b*sinh(e+f*x)^2)^(3/2)"),
        // 6.2 Hyperbolic cosine/6.2.1 (c+d x)^m (a+b cosh)^n.input:16
        parse!("cosh(a+b*x)/(c+d*x)"),
        // 6.2 Hyperbolic cosine/6.2.1 (c+d x)^m (a+b cosh)^n.input:74
        parse!("(c+d*x)^(3/2)*cosh(a+b*x)^3"),
        // 6.2 Hyperbolic cosine/6.2.1 (c+d x)^m (a+b cosh)^n.input:145
        parse!("(a+a*cosh(e+f*x))^2/(c+d*x)"),
        // 6.2 Hyperbolic cosine/6.2.1 (c+d x)^m (a+b cosh)^n.input:217
        parse!("(a+b*cosh(e+f*x))/(c+d*x)^2"),
        // 6.2 Hyperbolic cosine/6.2.2 (e x)^m (a+b x^n)^p cosh.input:22
        parse!("(a+b*x)^2*cosh(c+d*x)/x"),
        // 6.2 Hyperbolic cosine/6.2.2 (e x)^m (a+b x^n)^p cosh.input:82
        parse!("x^4*cosh(c+d*x)/(a+b*x^2)^2"),
        // 6.2 Hyperbolic cosine/6.2.3 (e x)^m (a+b cosh(c+d x^n))^p.input:17
        parse!("cosh(a+b*x^2)/x^2"),
        // 6.2 Hyperbolic cosine/6.2.4 (d+e x)^m cosh(a+b x+c x^2)^n.input:35
        parse!("cosh(1/4+x+x^2)^2"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:67
        parse!("(a+a*cosh(c+d*x))^(1/2)"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:110
        parse!("(a+b*cosh(c+d*x))^(1/2)"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:179
        parse!("1/(a*cosh(x)^3)^(3/2)"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:245
        parse!("coth(x)^2/(a+b*cosh(x))"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:313
        parse!("x*sinh(c+d*x)^3/(a+b*cosh(c+d*x))"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:380
        parse!("F^(c*(a+b*x))*cosh(d+e*x)"),
        // 6.2 Hyperbolic cosine/6.2.5 Hyperbolic cosine functions.input:415
        parse!("f^(a+c*x^2)*cosh(d+e*x+f*x^2)^2"),
        // 6.2 Hyperbolic cosine/6.2.7 hyper^m (a+b cosh^n)^p.input:69
        parse!("1/(a+b*cosh(x)^2)^3"),
        // 6.3 Hyperbolic tangent/6.3.1 (c+d x)^m (a+b tanh)^n.input:10
        parse!("(c+d*x)^3*tanh(e+f*x)"),
        // 6.3 Hyperbolic tangent/6.3.1 (c+d x)^m (a+b tanh)^n.input:108
        parse!("(c+d*x)^3/(a+b*tanh(e+f*x))^2"),
        // 6.3 Hyperbolic tangent/6.3.2 Hyperbolic tangent functions.input:79
        parse!("1/(a+a*tanh(c+d*x))^4"),
        // 6.3 Hyperbolic tangent/6.3.2 Hyperbolic tangent functions.input:116
        parse!("csch(x)^7/(1+tanh(x))"),
        // 6.3 Hyperbolic tangent/6.3.2 Hyperbolic tangent functions.input:182
        parse!("tanh(x)^2/(1+tanh(x))^(1/2)"),
        // 6.3 Hyperbolic tangent/6.3.2 Hyperbolic tangent functions.input:252
        parse!("tanh(a+b*log(c*x^n))^4/x"),
        // 6.3 Hyperbolic tangent/6.3.2 Hyperbolic tangent functions.input:330
        parse!("exp(c*(a+b*x))/(tanh(a*c+b*c*x)^2)^(5/2)"),
        // 6.3 Hyperbolic tangent/6.3.7 (d hyper)^m (a+b (c tanh)^n)^p.input:32
        parse!("csch(c+d*x)^3*(a+b*tanh(c+d*x)^2)^3"),
        // 6.3 Hyperbolic tangent/6.3.7 (d hyper)^m (a+b (c tanh)^n)^p.input:92
        parse!("sinh(c+d*x)^2/(a+b*tanh(c+d*x)^3)"),
        // 6.3 Hyperbolic tangent/6.3.7 (d hyper)^m (a+b (c tanh)^n)^p.input:156
        parse!("sech(c+d*x)/(a+b*tanh(c+d*x)^2)^3"),
        // 6.3 Hyperbolic tangent/6.3.7 (d hyper)^m (a+b (c tanh)^n)^p.input:223
        parse!("coth(c+d*x)^3/(a+b*tanh(c+d*x)^2)"),
        // 6.3 Hyperbolic tangent/6.3.7 (d hyper)^m (a+b (c tanh)^n)^p.input:287
        parse!("tanh(x)^4/(a+b*tanh(x)^2)^(1/2)"),
        // 6.4 Hyperbolic cotangent/6.4.1 (c+d x)^m (a+b coth)^n.input:12
        parse!("x*coth(a+b*x)"),
        // 6.4 Hyperbolic cotangent/6.4.2 Hyperbolic cotangent functions.input:20
        parse!("(b*coth(c+d*x))^(4/3)"),
        // 6.4 Hyperbolic cotangent/6.4.2 Hyperbolic cotangent functions.input:90
        parse!("(1+coth(x))^5"),
        // 6.4 Hyperbolic cotangent/6.4.2 Hyperbolic cotangent functions.input:154
        parse!("sech(x)^2*(1+coth(x))^(1/2)"),
        // 6.4 Hyperbolic cotangent/6.4.2 Hyperbolic cotangent functions.input:221
        parse!("coth(a+2*log(x))^2/x^3"),
        // 6.4 Hyperbolic cotangent/6.4.2 Hyperbolic cotangent functions.input:270
        parse!("(coth(a+b*log(c*x^n)))^(1/2)/x"),
        // 6.4 Hyperbolic cotangent/6.4.7 (d hyper)^m (a+b (c coth)^n)^p.input:55
        parse!("(1+coth(x)^2)^(1/2)"),
        // 6.5 Hyperbolic secant/6.5.2 (e x)^m (a+b sech(c+d x^n))^p.input:72
        parse!("x^3/(a+b*sech(c+d*(x)^(1/2)))^2"),
        // 6.5 Hyperbolic secant/6.5.3 Hyperbolic secant functions.input:26
        parse!("(b*sech(c+d*x))^(7/2)"),
        // 6.5 Hyperbolic secant/6.5.3 Hyperbolic secant functions.input:98
        parse!("csch(x)^4/(a+b*sech(x))"),
        // 6.5 Hyperbolic secant/6.5.3 Hyperbolic secant functions.input:146
        parse!("tanh(x)^6/(a+a*sech(x))"),
        // 6.5 Hyperbolic secant/6.5.3 Hyperbolic secant functions.input:214
        parse!("exp(c*(a+b*x))/(sech(a*c+b*c*x)^2)^(1/2)"),
        // 6.5 Hyperbolic secant/6.5.7 (d hyper)^m (a+b (c sech)^n)^p.input:12
        parse!("csch(c+d*x)*(a+b*sech(c+d*x)^2)"),
        // 6.5 Hyperbolic secant/6.5.7 (d hyper)^m (a+b (c sech)^n)^p.input:70
        parse!("cosh(c+d*x)^4*(a+b*sech(c+d*x)^2)^2"),
        // 6.5 Hyperbolic secant/6.5.7 (d hyper)^m (a+b (c sech)^n)^p.input:132
        parse!("coth(c+d*x)^3*(a+b*sech(c+d*x)^2)"),
        // 6.5 Hyperbolic secant/6.5.7 (d hyper)^m (a+b (c sech)^n)^p.input:165
        parse!("tanh(c+d*x)^3/(a+b*sech(c+d*x)^2)"),
        // 6.5 Hyperbolic secant/6.5.7 (d hyper)^m (a+b (c sech)^n)^p.input:222
        parse!("coth(x)*(a+b*sech(x)^2)^(3/2)"),
        // 6.6 Hyperbolic cosecant/6.6.2 (e x)^m (a+b csch(c+d x^n))^p.input:26
        parse!("x*csch(a+b*x^2)^7"),
        // 6.6 Hyperbolic cosecant/6.6.2 (e x)^m (a+b csch(c+d x^n))^p.input:115
        parse!("(e*x)^(-1+2*n)/(a+b*csch(c+d*x^n))^2"),
        // 6.6 Hyperbolic cosecant/6.6.3 Hyperbolic cosecant functions.input:80
        parse!("(a+1i*a*csch(c+d*x))^(5/2)"),
        // 6.6 Hyperbolic cosecant/6.6.3 Hyperbolic cosecant functions.input:122
        parse!("cosh(x)/(1i+csch(x))"),
        // 6.6 Hyperbolic cosecant/6.6.3 Hyperbolic cosecant functions.input:190
        parse!("csch(2*log(c*x))^(1/2)/x^2"),
        // 6.6 Hyperbolic cosecant/6.6.7 (d hyper)^m (a+b (c csch)^n)^p.input:26
        parse!("1/(a+b*csch(c+d*x)^2)^(7/2)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:55
        parse!("csch(a+b*x)^4*sech(a+b*x)^2"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:109
        parse!("sech(a+b*x)^4*tanh(a+b*x)^n"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:147
        parse!("coth(x)^4*csch(x)^6"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:203
        parse!("cosh(c+d*x)^2*sinh(a+b*x)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:260
        parse!("cosh(x)*tanh(4*x)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:320
        parse!("x*cosh(a+b*x)*sinh(a+b*x)^2"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:378
        parse!("x^3*sech(a+b*x)*sinh(a+b*x)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:411
        parse!("sech(a+b*x)^2*sinh(a+b*x)^2"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:528
        parse!("x*csch(a+b*x)*sech(a+b*x)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:646
        parse!("(a+b*csch(x))/(c+d*sinh(x))"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:707
        parse!("(sech(x)+1i*tanh(x))^5"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:765
        parse!("(csch(x)+sinh(x))^3"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:825
        parse!("cosh(x)^3*sinh(x)/(a*cosh(x)+b*sinh(x))"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:885
        parse!("1/(a+b*cosh(x)+c*sinh(x))^(1/2)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:947
        parse!("1/(sech(x)^2+tanh(x)^2)^3"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:1012
        parse!("x^3/(a+b*cosh(x)*sinh(x))"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:1088
        parse!("exp(2*(a+b*x))*cosh(a+b*x)*sinh(a+b*x)^3"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:1130
        parse!("exp(c+d*x)*cosh(a+b*x)^2"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:1200
        parse!("exp(n*sinh(1/2*(a+b*x)))*sinh(a+b*x)"),
        // 6.7 Miscellaneous/6.7.1 Hyperbolic functions.input:1270
        parse!("(-csch(a+b*x)^4+sech(a+b*x)^4)/(csch(a+b*x)^4+sech(a+b*x)^4)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
