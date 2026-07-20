// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 3 Logarithms. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_3_logarithms() {
    let samples = [
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:10
        parse!("x^3*log(c*x)"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:42
        parse!("x/log(c*x)^2"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:68
        parse!("(a+b*log(c*x^n))^2"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:101
        parse!("1/(a+b*log(c*x^n))^3"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:142
        parse!("x^2*(log(a*x^n))^(1/2)"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:162
        parse!("1/(x^2*(log(a*x^n))^(1/2))"),
        // 3.1.2 (d x)^m (a+b log(c x^n))^p.input:195
        parse!("x^m/log(a*x^n)^(1/2)"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:13
        parse!("x^2*(d+e*x)*(a+b*log(c*x^n))"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:35
        parse!("(d+e*x)^3*(a+b*log(c*x^n))/x^2"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:67
        parse!("x^4*(a+b*log(c*x^n))/(d+e*x)^4"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:102
        parse!("x*(d+e*x)^2*(a+b*log(c*x^n))^2"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:135
        parse!("x*(a+b*log(c*x^n))^2/(d+e*x)^4"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:184
        parse!("(a+b*log(c*x^n))/(d+e*x)^(1/2)"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:243
        parse!("x^2*(d+e*x^2)^2*(a+b*log(c*x^n))"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:276
        parse!("x^5*(a+b*log(c*x^n))/(d+e*x^2)^2"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:295
        parse!("(a+b*log(c*x^n))/(x^4*(d+e*x^2)^3)"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:348
        parse!("(d+e*x^2)^(3/2)*(a+b*log(c*x^n))/x^4"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:380
        parse!("(a+b*log(c*x^n))/(x*(d+e*x^2)^(5/2))"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:425
        parse!("(a+b*log(c*x^n))/(d+e/x)"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:462
        parse!("(f*x)^(-1+m)*(a+b*log(c*x^n))^2/(d+e*x^m)"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:499
        parse!("x*(d+e*x^r)^3*(a+b*log(c*x^n))"),
        // 3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.input:552
        parse!("(a+b*log(c*x^n))/(x*(d+e*x^r)^(3/2))"),
        // 3.1.5 u (a+b log(c x^n))^p.input:25
        parse!("x*(a+b*log(c*x^n))^2*log(1+e*x)"),
        // 3.1.5 u (a+b log(c x^n))^p.input:58
        parse!("(a+b*log(c*x^n))^3*log(d*(1/d+f*x^2))/x^3"),
        // 3.1.5 u (a+b log(c x^n))^p.input:84
        parse!("(a+b*log(c*x^n))^3*log(d*(1/d+f*x^m))/x"),
        // 3.1.5 u (a+b log(c x^n))^p.input:120
        parse!("x^2*(a+b*log(c*x^n))*log(d*(e+f*x^2)^m)"),
        // 3.1.5 u (a+b log(c x^n))^p.input:153
        parse!("(a+b*log(c*x^n))^2*log(d*(e+f*(x)^(1/2)))/x^2"),
        // 3.1.5 u (a+b log(c x^n))^p.input:203
        parse!("(a+b*log(c*x^n))^2*(d+e*log(f*x^r))/x"),
        // 3.1.5 u (a+b log(c x^n))^p.input:231
        parse!("(d+e*x^2)*atan(a*x)*log(c*x^n)"),
        // 3.1.5 u (a+b log(c x^n))^p.input:268
        parse!("(a+b*log(c*x^n))*polylog(3,e*x)/x^3"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:12
        parse!("(a*g+b*g*x)^4*(A+B*log(e*((a+b*x)/(c+d*x))^n))"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:51
        parse!("(c*g+d*g*x)*(A+B*log(e*((a+b*x)/(c+d*x))^n))"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:90
        parse!("(A+B*log(e*((a+b*x)/(c+d*x))^n))/(f+g*x)^2"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:140
        parse!("(A+B*log(e*(a+b*x)/(c+d*x)))^2/(a*g+b*g*x)^3"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:167
        parse!("(A+B*log(e*(a+b*x)^2/(c+d*x)^2))/(a*g+b*g*x)^2"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:213
        parse!("(a+b*x)^3*(A+B*log(e*(a+b*x)^n/(c+d*x)^n))^3"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:254
        parse!("1/((a*g+b*g*x)^3*(A+B*log(e*(c+d*x)/(a+b*x))))"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:280
        parse!("(A+B*log(e*(c+d*x)^2/(a+b*x)^2))^2/(a*g+b*g*x)^4"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:352
        parse!("(A+B*log(e*(a+b*x)^2/(c+d*x)^2))/(f+g*x)^3"),
        // 3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.input:399
        parse!("(g+h*x)*(A+B*log(e*(a+b*x)^n/(c+d*x)^n))^3"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:28
        parse!("(c*i+d*i*x)^2*(A+B*log(e*(a+b*x)/(c+d*x)))/(a*g+b*g*x)^4"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:61
        parse!("(a*g+b*g*x)^2*(A+B*log(e*(a+b*x)/(c+d*x)))/(c*i+d*i*x)^3"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:96
        parse!("(c*i+d*i*x)^3*(A+B*log(e*(a+b*x)/(c+d*x)))^2/(a*g+b*g*x)^2"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:133
        parse!("(a*g+b*g*x)*(c*i+d*i*x)*(A+B*log(e*((a+b*x)/(c+d*x))^n))"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:151
        parse!("(a*g+b*g*x)^2*(c*i+d*i*x)^3*(A+B*log(e*((a+b*x)/(c+d*x))^n))"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:188
        parse!("(a*g+b*g*x)^3*(c*i+d*i*x)*(A+B*log(e*((a+b*x)/(c+d*x))^n))^2"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:221
        parse!("(A+B*log(e*((a+b*x)/(c+d*x))^n))^2/((a*g+b*g*x)*(c*i+d*i*x))"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:245
        parse!("(a*g+b*g*x)^m*(c*i+d*i*x)^(-2-m)*(A+B*log(e*((a+b*x)/(c+d*x))^n))^3"),
        // 3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.input:290
        parse!("(a+b*x)/((c+d*x)^3*log(e*((a+b*x)/(c+d*x))^n))"),
        // 3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.input:25
        parse!("(a+b*x)*log(e*(f*(a+b*x)^p*(c+d*x)^q)^r)"),
        // 3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.input:49
        parse!("log(e*(f*(a+b*x)^p*(c+d*x)^q)^r)/(g+h*x)^3"),
        // 3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.input:115
        parse!("x*log(e*((a+b*x)/(c+d*x))^n)/(f+g*x+h*x^2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:16
        parse!("1/log(c*(d+e*x))^3"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:45
        parse!("(a+b*log(c*(d+e*x)^n))^(1/2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:86
        parse!("(a+b*log(c*(d+e*x)^n))^3/(f+g*x)^2"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:119
        parse!("(f+g*x)^3/(a+b*log(c*(d+e*x)^n))"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:153
        parse!("(f+g*x)*(a+b*log(c*(d+e*x)^n))^(5/2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:190
        parse!("(a+b*log(c*(d+e*x)^n))^2/(f+g*x)^(5/2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:242
        parse!("(a+b*log(c*(e+f*x)))/((d*e+d*f*x)*(h+i*x))"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:286
        parse!("(h+i*x)^2*(a+b*log(c*(e+f*x)))^p/(d*e+d*f*x)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:314
        parse!("(a+b*log(c*(d+e*x)^n))^3/((f+g*x)*(h+i*x)^2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:363
        parse!("(a+b*log(c*(d+e*x)^n))/(x^2*(f+g*x^2))"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:405
        parse!("x^3*log(c+d*x)/(a+b*x^4)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:441
        parse!("x^2*(a+b*log(c*(d+e*x)^n))^2/(f+g*x^2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:484
        parse!("log(c*(a+b*x)^n)^3/(d+e*x+f*x^2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:529
        parse!("log(a+b*x)*log(c+d*x)/x"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:584
        parse!("1/(a+b*log(c*(d*(e+f*x)^m)^n))^2"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:625
        parse!("(a+b*log(c*(d*(e+f*x)^p)^q))^3/(g+h*x)^3"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:673
        parse!("1/(a+b*log(c*(d*(e+f*x)^p)^q))^(5/2)"),
        // 3.3 u (a+b log(c (d+e x)^n))^p.input:745
        parse!("(i+j*x)^3*(a+b*log(c*(d*(e+f*x)^p)^q))/(g+h*x)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:27
        parse!("x^2*log(c*(a+b*x^3)^p)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:64
        parse!("x^2*log(c*(a+b*(x)^(1/2))^p)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:98
        parse!("(f*x)^(-1-2*n)*log(c*(d+e*x^n)^p)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:146
        parse!("x^3/log(c*(a+b*x^2)^p)^2"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:192
        parse!("x^5/log(c*(d+e*x^3)^p)^2"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:245
        parse!("(d+e*x)^2*log(c*(a+b*x^3)^p)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:288
        parse!("log(c*(a+b*x)^p)/(x*(d+e*x))"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:321
        parse!("x^3*log(c*(a+b/x^3)^p)/(d+e*x)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:385
        parse!("(f+g*x^3)^2*log(c*(d+e*x^2)^p)^2"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:424
        parse!("x*(f+g*x^2)^2*log(c*(d+e*x^2)^p)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:457
        parse!("log(c*(d+e*x^2)^p)/(x^2*(f+g*x^2)^2)"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:522
        parse!("(f*x)^q*(a+b*log(c*(d+e*x^m)^n))"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:546
        parse!("(a+b*log(c*(d+e*(x)^(1/2))^n))^3"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:583
        parse!("(a+b*log(c*(d+e*x^(1/3))^n))/x^3"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:616
        parse!("(a+b*log(c*(d+e*x^(2/3))^n))^2/x^4"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:640
        parse!("(a+b*log(c*(d+e/x^(1/3))^n))^2/x^2"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:679
        parse!("x^3*(a+b*log(c*(d+e*(x)^(1/2))))^p"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:715
        parse!("x^3*(a+b*log(c*(d+e*x^(1/3))^2))^p"),
        // 3.4 u (a+b log(c (d+e x^m)^n))^p.input:780
        parse!("(f+g*x)^2*(a+b*log(c*(d+e*x^2)^p))/(h*x)^(9/2)"),
        // 3.5 Logarithm functions.input:14
        parse!("log(c*x^n)^(-1+q)/x"),
        // 3.5 Logarithm functions.input:75
        parse!("(a+b*log(c*log(d*x^n)^p))/x^4"),
        // 3.5 Logarithm functions.input:112
        parse!("(d+e*x)*log(d*(a+b*x+c*x^2)^n)"),
        // 3.5 Logarithm functions.input:142
        parse!("log(-1+4*x+4*((-1+x)*x)^(1/2))/x^3"),
        // 3.5 Logarithm functions.input:177
        parse!("log(log(6*x))/(x*log(6*x))"),
        // 3.5 Logarithm functions.input:213
        parse!("log(a*tan(x)^2)"),
        // 3.5 Logarithm functions.input:235
        parse!("cos(x)*log(sin(x))"),
        // 3.5 Logarithm functions.input:272
        parse!("cosh(a+b*x)*log(cosh(1/2*a+1/2*b*x)*sinh(1/2*a+1/2*b*x))"),
        // 3.5 Logarithm functions.input:321
        parse!("1/(a*x+b*x*log(c*x^n)^3)"),
        // 3.5 Logarithm functions.input:342
        parse!("log(x+(x)^(1/2))"),
        // 3.5 Logarithm functions.input:379
        parse!("(A+B*log(x))/(a-b*log(x))^(1/2)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
