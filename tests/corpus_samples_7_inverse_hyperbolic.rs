// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 7 Inverse hyperbolic functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_7_inverse_hyperbolic() {
    let samples = [
        // 7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b asinh(c x))^n.input:12
        parse!("x^4*asinh(a*x)"),
        // 7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b asinh(c x))^n.input:80
        parse!("x^4/asinh(a*x)^4"),
        // 7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b asinh(c x))^n.input:156
        parse!("asinh(a*x)^n"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:35
        parse!("(d+c^2*d*x^2)^3*(a+b*asinh(c*x))/x"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:109
        parse!("x^5*(a+b*asinh(c*x))/(pi+pi*c^2*x^2)^(3/2)"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:181
        parse!("x^4*(a+b*asinh(c*x))/(d+c^2*d*x^2)^(3/2)"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:256
        parse!("(d+c^2*d*x^2)^3*(a+b*asinh(c*x))^2/x^3"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:332
        parse!("asinh(a*x)^2/(x^3*(1+a^2*x^2)^(1/2))"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:418
        parse!("x^4*(1+c^2*x^2)^(1/2)/(a+b*asinh(c*x))"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:496
        parse!("x*(1+c^2*x^2)^(3/2)/(a+b*asinh(c*x))^2"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:653
        parse!("(d+1i*c*d*x)^(5/2)*(a+b*asinh(c*x))*(f-1i*c*f*x)^(1/2)"),
        // 7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b asinh(c x))^n.input:728
        parse!("(d+1i*c*d*x)^(3/2)*(a+b*asinh(c*x))^2/(f-1i*c*f*x)^(5/2)"),
        // 7.1 Inverse hyperbolic sine/7.1.5 Inverse hyperbolic sine functions.input:21
        parse!("(d+e*x)^3*(a+b*asinh(c*x))"),
        // 7.1 Inverse hyperbolic sine/7.1.5 Inverse hyperbolic sine functions.input:145
        parse!("x/asinh(a+b*x)^3"),
        // 7.1 Inverse hyperbolic sine/7.1.5 Inverse hyperbolic sine functions.input:245
        parse!("(c*e+d*e*x)^2/(a+b*asinh(c+d*x))^4"),
        // 7.1 Inverse hyperbolic sine/7.1.5 Inverse hyperbolic sine functions.input:322
        parse!("(a+b*asinh(c+d*x))^2/(c*e+d*e*x)^(7/2)"),
        // 7.1 Inverse hyperbolic sine/7.1.5 Inverse hyperbolic sine functions.input:406
        parse!("x*asinh(a*x^n)"),
        // 7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b acosh(c x))^n.input:15
        parse!("x*acosh(a*x)"),
        // 7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b acosh(c x))^n.input:116
        parse!("x^4/acosh(a*x)^(3/2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b acosh(c x))^n.input:204
        parse!("(a+b*acosh(c*x))^2*(f*x)^(1/2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:81
        parse!("(a+b*acosh(c*x))*(d-c^2*d*x^2)^(1/2)/x^8"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:129
        parse!("(a+b*acosh(c*x))/(x*(d-c^2*d*x^2)^(1/2))"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:233
        parse!("x^3*(a+b*acosh(c*x))^2/(d-c^2*d*x^2)^(1/2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:323
        parse!("(c-a^2*c*x^2)^2/acosh(a*x)"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:515
        parse!("(c-a^2*c*x^2)^(1/2)/acosh(a*x)^(5/2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b acosh(c x))^n.input:601
        parse!("x^2*(d+e*x^2)^3*(a+b*acosh(c*x))"),
        // 7.2 Inverse hyperbolic cosine/7.2.5 Inverse hyperbolic cosine functions.input:16
        parse!("acosh(c*x)/(d+e*x)^2"),
        // 7.2 Inverse hyperbolic cosine/7.2.5 Inverse hyperbolic cosine functions.input:70
        parse!("acosh(a*x)/(c+d*x^2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.5 Inverse hyperbolic cosine functions.input:182
        parse!("(a+b*acosh(c+d*x))^2/(c*e+d*e*x)^3"),
        // 7.2 Inverse hyperbolic cosine/7.2.5 Inverse hyperbolic cosine functions.input:257
        parse!("1/(a+b*acosh(c+d*x))^(1/2)"),
        // 7.2 Inverse hyperbolic cosine/7.2.5 Inverse hyperbolic cosine functions.input:378
        parse!("(a+b*acosh((1-c*x)^(1/2)/(1+c*x)^(1/2)))/(1-c^2*x^2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.2 (d x)^m (a+b atanh(c x^n))^p.input:52
        parse!("(a+b*atanh(c*x))/(d*x)^(7/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.2 (d x)^m (a+b atanh(c x^n))^p.input:140
        parse!("x^3*(a+b*atanh(c*x^3))"),
        // 7.3 Inverse hyperbolic tangent/7.3.2 (d x)^m (a+b atanh(c x^n))^p.input:209
        parse!("(a+b*atanh(c/x))^3/x"),
        // 7.3 Inverse hyperbolic tangent/7.3.2 (d x)^m (a+b atanh(c x^n))^p.input:293
        parse!("(a+b*atanh(c*x^(3/2)))/x^4"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:25
        parse!("(d+c*d*x)^2*(a+b*atanh(c*x))/x"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:97
        parse!("(d+c*d*x)^2*(a+b*atanh(c*x))^2/x"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:180
        parse!("x^3*(a+b*atanh(c*x))/(d+e*x)"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:242
        parse!("x^3*(1-a^2*x^2)^2*atanh(a*x)"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:329
        parse!("x^2*atanh(a*x)/(1-a^2*x^2)^2"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:403
        parse!("x/((1-a^2*x^2)^3*atanh(a*x))"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:485
        parse!("atanh(a*x)/(x*(1-a^2*x^2)^(3/2))"),
        // 7.3 Inverse hyperbolic tangent/7.3.4 u (a+b atanh(c x))^p.input:589
        parse!("atanh(a*x)^3/(1-a^2*x^2)^(9/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.5 u (a+b atanh(c+d x))^p.input:16
        parse!("atanh(a+b*x)^2/x^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.5 u (a+b atanh(c+d x))^p.input:72
        parse!("atanh(a+b*x)/(c+d*x^3)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:70
        parse!("1/(exp(3*atanh(a*x))*x^3)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:147
        parse!("exp(1/3*atanh(x))/x"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:231
        parse!("exp(4*atanh(a*x))*(c-a*c*x)^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:305
        parse!("(c-a*c*x)^(1/2)/exp(atanh(a*x))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:378
        parse!("exp(atanh(a*x))*(c-a*c*x)^4/x^4"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:426
        parse!("exp(atanh(x))*x/(1+x)^2"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:502
        parse!("(c-a*c*x)^(1/2)/(exp(3*atanh(a*x))*x^4)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:579
        parse!("(c-c/(a*x))^3/exp(3*atanh(a*x))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:661
        parse!("exp(atanh(a*x))*(c-c/(a*x))^(1/2)/x"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:737
        parse!("exp(atanh(a*x))/(c-c/(a^2*x^2))^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:810
        parse!("exp(2*atanh(a*x))/(c-c/(a^2*x^2))^(3/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:851
        parse!("1/(exp(3*atanh(a*x))*(c-c/(a^2*x^2))^(7/2))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:928
        parse!("(c-c/(a^2*x^2))^p/exp(3*atanh(a*x))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1028
        parse!("exp(atanh(a+b*x))/(x*(1-a^2-2*a*b*x-b^2*x^2))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1112
        parse!("exp(atanh(a*x))*x^5/(1-a^2*x^2)^(5/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1189
        parse!("exp(atanh(a*x))*x^2*(1-a^2*x^2)^p"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1263
        parse!("exp(2*atanh(a*x))/(c-a^2*c*x^2)^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1315
        parse!("exp(2*atanh(a*x))*x/(c-a^2*c*x^2)^(3/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1410
        parse!("exp(4*atanh(a*x))*(c-a^2*c*x^2)^2"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1516
        parse!("1/(exp(2*atanh(a*x))*(c-a^2*c*x^2)^(7/2))"),
        // 7.3 Inverse hyperbolic tangent/7.3.6 Exponentials of inverse hyperbolic tangent functions.input:1624
        parse!("exp(n*atanh(a*x))/(x^2*(c-a^2*c*x^2))"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:15
        parse!("atanh(x*(e)^(1/2)/(d+e*x^2)^(1/2))/x^5"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:75
        parse!("atanh(tanh(a+b*x))^2/x^4"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:147
        parse!("(atanh(tanh(a+b*x)))^(1/2)/x^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:220
        parse!("x^(3/2)*atanh(tanh(a+b*x))^3"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:294
        parse!("x^(3/2)/atanh(tanh(a+b*x))^(3/2)"),
        // 7.3 Inverse hyperbolic tangent/7.3.7 Inverse hyperbolic tangent functions.input:384
        parse!("x^2*atanh(c+d*tan(a+b*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.1 Inverse hyperbolic cotangent functions.input:94
        parse!("x^3*acoth(a+b*x)^2"),
        // 7.4 Inverse hyperbolic cotangent/7.4.1 Inverse hyperbolic cotangent functions.input:162
        parse!("(e+f*x)^2*(a+b*acoth(c+d*x))^2"),
        // 7.4 Inverse hyperbolic cotangent/7.4.1 Inverse hyperbolic cotangent functions.input:240
        parse!("x^m/acoth(tanh(a+b*x))^3"),
        // 7.4 Inverse hyperbolic cotangent/7.4.1 Inverse hyperbolic cotangent functions.input:331
        parse!("acoth(1-1i*d+d*tan(a+b*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:19
        parse!("exp(acoth(a*x))/x^4"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:98
        parse!("exp(5/2*acoth(a*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:180
        parse!("exp(1/4*acoth(a*x))*x^m"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:228
        parse!("exp(4*acoth(a*x))*(c-a*c*x)^p"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:302
        parse!("(c-a*c*x)^(7/2)/exp(acoth(a*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:379
        parse!("exp(acoth(x))*(1+x)^(3/2)"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:455
        parse!("exp(acoth(a*x))/(c-c/(a*x))^4"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:527
        parse!("exp(2*acoth(a*x))/(c-c/(a*x))^(3/2)"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:602
        parse!("(c-c/(a*x))^(1/2)/exp(acoth(a*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:658
        parse!("exp(2*acoth(a*x))*(c-a^2*c*x^2)^4"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:730
        parse!("exp(2*acoth(a*x))/(c-a^2*c*x^2)^(7/2)"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:803
        parse!("exp(acoth(a*x))/(x^3*(c-a^2*c*x^2)^(3/2))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:877
        parse!("(c-a^2*c*x^2)^p/exp(2*p*acoth(a*x))"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:955
        parse!("exp(acoth(a*x))*(c-c/(a^2*x^2))^(7/2)"),
        // 7.4 Inverse hyperbolic cotangent/7.4.2 Exponentials of inverse hyperbolic cotangent functions.input:1028
        parse!("exp(3*acoth(a*x))*x*(c-c/(a^2*x^2))^(1/2)"),
        // 7.5 Inverse hyperbolic secant/7.5.1 u (a+b asech(c x))^n.input:17
        parse!("asech(a*x)^2/x^3"),
        // 7.5 Inverse hyperbolic secant/7.5.1 u (a+b asech(c x))^n.input:97
        parse!("(d+e*x)^3*(a+b*asech(c*x))"),
        // 7.5 Inverse hyperbolic secant/7.5.1 u (a+b asech(c x))^n.input:186
        parse!("x*(d+e*x^2)^(3/2)*(a+b*asech(c*x))"),
        // 7.5 Inverse hyperbolic secant/7.5.2 Inverse hyperbolic secant functions.input:24
        parse!("asech(a+b*x)^3/x"),
        // 7.5 Inverse hyperbolic secant/7.5.2 Inverse hyperbolic secant functions.input:118
        parse!("1/(exp(asech(a*x))*x^3)"),
        // 7.6 Inverse hyperbolic cosecant/7.6.1 u (a+b acsch(c x))^n.input:71
        parse!("(a+b*acsch(c*x))/(d+e*x)^3"),
        // 7.6 Inverse hyperbolic cosecant/7.6.1 u (a+b acsch(c x))^n.input:133
        parse!("(d+e*x^2)^2*(a+b*acsch(c*x))/x"),
        // 7.6 Inverse hyperbolic cosecant/7.6.2 Inverse hyperbolic cosecant functions.input:11
        parse!("acsch(a+b*x)/x"),
        // 7.6 Inverse hyperbolic cosecant/7.6.2 Inverse hyperbolic cosecant functions.input:96
        parse!("x^(-1+n)*acsch(a+b*x^n)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
