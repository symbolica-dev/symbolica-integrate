// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 5 Inverse trig functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_5_inverse_trig() {
    let samples = [
        // 5.1 Inverse sine/5.1.2 (d x)^m (a+b asin(c x))^n.input:12
        parse!("x^4*asin(a*x)"),
        // 5.1 Inverse sine/5.1.2 (d x)^m (a+b asin(c x))^n.input:44
        parse!("x^4*asin(a*x)^4"),
        // 5.1 Inverse sine/5.1.2 (d x)^m (a+b asin(c x))^n.input:111
        parse!("x^4/(asin(a*x))^(1/2)"),
        // 5.1 Inverse sine/5.1.2 (d x)^m (a+b asin(c x))^n.input:205
        parse!("1/(a+b*asin(c*x))^3"),
        // 5.1 Inverse sine/5.1.2 (d x)^m (a+b asin(c x))^n.input:239
        parse!("x^2/(a+b*asin(c*x))^(5/2)"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:48
        parse!("(a+b*asin(c*x))/(x^3*(d-c^2*d*x^2))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:80
        parse!("x^3*(d-c^2*d*x^2)^(1/2)*(a+b*asin(c*x))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:132
        parse!("x*(a+b*asin(c*x))/(d-c^2*d*x^2)^(1/2)"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:166
        parse!("(f*x)^(3/2)*(a+b*asin(c*x))/(1-c^2*x^2)^(1/2)"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:206
        parse!("(d-c^2*d*x^2)^2*(a+b*asin(c*x))^2/x^4"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:258
        parse!("x^2*(d-c^2*d*x^2)^(3/2)*(a+b*asin(c*x))^2"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:292
        parse!("(a+b*asin(c*x))^2/(x^2*(d-c^2*d*x^2)^(3/2))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:321
        parse!("x^m*(d-c^2*d*x^2)*(a+b*asin(c*x))^2"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:405
        parse!("x^3/(asin(a*x)*(1-a^2*x^2)^(1/2))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:523
        parse!("(d-c^2*d*x^2)/(a+b*asin(c*x))^(3/2)"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:561
        parse!("asin(x/a)^(3/2)/(a^2-x^2)^(1/2)"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:649
        parse!("(a+b*asin(c*x))/((d+c*d*x)^(3/2)*(f-c*f*x)^(1/2))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:681
        parse!("(d+c*d*x)^(1/2)*(e-c*e*x)^(5/2)*(a+b*asin(c*x))^2"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:744
        parse!("x*(d+e*x^2)*(a+b*asin(c*x))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:779
        parse!("(a+b*asin(c*x))/(x^4*(d+e*x^2))"),
        // 5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b asin(c x))^n.input:848
        parse!("(d+e*x^2)^2/(a+b*asin(c*x))^2"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:57
        parse!("(a+b*asin(c*x))*(d-c^2*d*x^2)^(1/2)/(f+g*x)"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:107
        parse!("(f+g*x)^3*(d-c^2*d*x^2)^(5/2)*(a+b*asin(c*x))^2"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:161
        parse!("(d+e*x)^2*(f+g*x+h*x^2)*(a+b*asin(c*x))"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:223
        parse!("x/asin(a+b*x)"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:283
        parse!("(c*e+d*e*x)^2*(a+b*asin(c+d*x))^2"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:317
        parse!("(c*e+d*e*x)^3/(a+b*asin(c+d*x))^2"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:369
        parse!("(c*e+d*e*x)/(a+b*asin(c+d*x))^(3/2)"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:401
        parse!("(a+b*asin(c+d*x))^2/(c*e+d*e*x)^(3/2)"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:465
        parse!("x^5*(a+b*asin(c*x^2))"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:499
        parse!("(a+b*asin(c/x))/x"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:539
        parse!("1/(a+b*asin(1+d*x^2))^2"),
        // 5.1 Inverse sine/5.1.5 Inverse sine functions.input:597
        parse!("exp(asin(a+b*x))*x^2"),
        // 5.2 Inverse cosine/5.2.2 (d x)^m (a+b acos(c x))^n.input:16
        parse!("acos(a*x)"),
        // 5.2 Inverse cosine/5.2.2 (d x)^m (a+b acos(c x))^n.input:48
        parse!("acos(a*x)^4"),
        // 5.2 Inverse cosine/5.2.2 (d x)^m (a+b acos(c x))^n.input:100
        parse!("x*acos(a*x)^(3/2)"),
        // 5.2 Inverse cosine/5.2.2 (d x)^m (a+b acos(c x))^n.input:176
        parse!("a+b*acos(c*x)"),
        // 5.2 Inverse cosine/5.2.2 (d x)^m (a+b acos(c x))^n.input:230
        parse!("x/(a+b*acos(c*x))^(1/2)"),
        // 5.2 Inverse cosine/5.2.4 (f x)^m (d+e x^2)^p (a+b acos(c x))^n.input:41
        parse!("(c+d*x^2)^4*acos(a*x)"),
        // 5.2 Inverse cosine/5.2.5 Inverse cosine functions.input:62
        parse!("x^2*acos(a+b*x)"),
        // 5.2 Inverse cosine/5.2.5 Inverse cosine functions.input:130
        parse!("x^3*acos(a+b*x^4)"),
        // 5.2 Inverse cosine/5.2.5 Inverse cosine functions.input:164
        parse!("1/(a+b*acos(-1+d*x^2))^(5/2)"),
        // 5.3 Inverse tangent/5.3.2 (d x)^m (a+b atan(c x^n))^p.input:24
        parse!("x^5*(a+b*atan(c*x))^2"),
        // 5.3 Inverse tangent/5.3.2 (d x)^m (a+b atan(c x^n))^p.input:151
        parse!("x^3*(a+b*atan(c*x^3))"),
        // 5.3 Inverse tangent/5.3.2 (d x)^m (a+b atan(c x^n))^p.input:206
        parse!("(a+b*atan(c/x))/x^2"),
        // 5.3 Inverse tangent/5.3.2 (d x)^m (a+b atan(c x^n))^p.input:235
        parse!("atan((x)^(1/2))/x^(5/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:24
        parse!("(d+1i*c*d*x)^2*(a+b*atan(c*x))"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:58
        parse!("x*(a+b*atan(c*x))/(d+1i*c*d*x)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:94
        parse!("x^2*(d+1i*c*d*x)^2*(a+b*atan(c*x))^2"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:144
        parse!("(a+b*atan(c*x))^3/(d+1i*c*d*x)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:192
        parse!("x*(c+a^2*c*x^2)*atan(a*x)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:239
        parse!("atan(a*x)/(x*(c+a^2*c*x^2)^3)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:278
        parse!("atan(a*x)/(x^2*(c+a^2*c*x^2)^(1/2))"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:318
        parse!("(c+a^2*c*x^2)*atan(a*x)^2"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:370
        parse!("x^3*atan(a*x)^2*(c+a^2*c*x^2)^(1/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:404
        parse!("x^3*atan(a*x)^2/(c+a^2*c*x^2)^(3/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:439
        parse!("(c+a^2*c*x^2)*atan(a*x)^3"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:491
        parse!("x^3*atan(a*x)^3*(c+a^2*c*x^2)^(1/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:525
        parse!("x^3*atan(a*x)^3/(c+a^2*c*x^2)^(3/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:695
        parse!("1/((c+a^2*c*x^2)^(3/2)*atan(a*x)^2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:899
        parse!("x^2*(atan(a*x))^(1/2)/(c+a^2*c*x^2)^(5/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:1152
        parse!("1/((c+a^2*c*x^2)^(3/2)*(atan(a*x))^(1/2))"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:1350
        parse!("(d+e*x^2)*(a+b*atan(c*x))/x^2"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:1384
        parse!("x^3*(a+b*atan(c*x))/(d+e*x^2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:1450
        parse!("x*(a+b*atan(c*x))/(d+e*x^2)^(3/2)"),
        // 5.3 Inverse tangent/5.3.4 u (a+b atan(c x))^p.input:1521
        parse!("x*(a+b*atan(c*x))^2/(d+e*x^2)^2"),
        // 5.3 Inverse tangent/5.3.5 u (a+b atan(c+d x))^p.input:10
        parse!("(c*e+d*e*x)^3*(a+b*atan(c+d*x))"),
        // 5.3 Inverse tangent/5.3.5 u (a+b atan(c+d x))^p.input:46
        parse!("(a+b*atan(c+d*x))^2"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:18
        parse!("exp(1i*atan(a*x))/x^4"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:48
        parse!("x/exp(1i*atan(a*x))"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:84
        parse!("exp(1/2*1i*atan(a*x))/x^6"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:136
        parse!("exp(1/3*1i*atan(x))*x^2"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:178
        parse!("x^m/exp(1/2*1i*atan(a*x))"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:234
        parse!("1/exp(1i*atan(a+b*x))"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:265
        parse!("exp(1/2*1i*atan(a+b*x))/x^2"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:306
        parse!("exp(atan(a*x))*(c+a^2*c*x^2)^(3/2)"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:357
        parse!("1/(exp(2*atan(a*x))*(c+a^2*c*x^2)^(3/2))"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:396
        parse!("exp(2*1i*atan(a*x))/(c+a^2*c*x^2)^(3/2)"),
        // 5.3 Inverse tangent/5.3.6 Exponentials of inverse tangent.input:489
        parse!("exp(n*atan(a*x))/(c+a^2*c*x^2)^(4/3)"),
        // 5.3 Inverse tangent/5.3.7 Inverse tangent functions.input:37
        parse!("atan(x*(-e)^(1/2)/(d+e*x^2)^(1/2))/x^(15/2)"),
        // 5.3 Inverse tangent/5.3.7 Inverse tangent functions.input:98
        parse!("x^2*atan(c+(-1-1i*c)*cot(a+b*x))"),
        // 5.3 Inverse tangent/5.3.7 Inverse tangent functions.input:156
        parse!("x^2*atan(exp(a+b*x))"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:19
        parse!("acot(a*x)/x^2"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:51
        parse!("x^m*acot(a*x)"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:113
        parse!("acot(a*x^2)"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:167
        parse!("acot(a+b*x)/(1+a^2+2*a*b*x+b^2*x^2)^(1/2)"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:233
        parse!("acot(c+d*tan(a+b*x))"),
        // 5.4 Inverse cotangent/5.4.1 Inverse cotangent functions.input:291
        parse!("x*acot(c+d*coth(a+b*x))"),
        // 5.4 Inverse cotangent/5.4.2 Exponentials of inverse cotangent.input:11
        parse!("exp(acot(x))/(a+a*x^2)^3"),
        // 5.5 Inverse secant/5.5.1 u (a+b asec(c x))^n.input:30
        parse!("(a+b*asec(c*x))^2/x"),
        // 5.5 Inverse secant/5.5.1 u (a+b asec(c x))^n.input:118
        parse!("(d+e*x^2)^2*(a+b*asec(c*x))/x^2"),
        // 5.5 Inverse secant/5.5.1 u (a+b asec(c x))^n.input:156
        parse!("x^5*(a+b*asec(c*x))*(d+e*x^2)^(1/2)"),
        // 5.5 Inverse secant/5.5.1 u (a+b asec(c x))^n.input:190
        parse!("x*(a+b*asec(c*x))/(d+e*x^2)^(3/2)"),
        // 5.5 Inverse secant/5.5.2 Inverse secant functions.input:28
        parse!("asec(a/x)/x^3"),
        // 5.5 Inverse secant/5.5.2 Inverse secant functions.input:74
        parse!("exp(asec(a*x))/x^2"),
        // 5.6 Inverse cosecant/5.6.1 u (a+b acsc(c x))^n.input:86
        parse!("x^3*(a+b*acsc(c*x))/(d+e*x)^(1/2)"),
        // 5.6 Inverse cosecant/5.6.1 u (a+b acsc(c x))^n.input:124
        parse!("(d+e*x^2)^2*(a+b*acsc(c*x))"),
        // 5.6 Inverse cosecant/5.6.1 u (a+b acsc(c x))^n.input:191
        parse!("x^3*(a+b*acsc(c*x))/(d+e*x^2)^(3/2)"),
        // 5.6 Inverse cosecant/5.6.2 Inverse cosecant functions.input:31
        parse!("acsc(a*x^n)/x"),
        // 5.6 Inverse cosecant/5.6.2 Inverse cosecant functions.input:80
        parse!("acsc(a+b*x)/(a*d/b+d*x)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
