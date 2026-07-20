// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 1 Algebraic functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_1_algebraic() {
    let samples = [
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:10
        parse!("0"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:300
        parse!("1/(x^2*(4+6*x)^2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:590
        parse!("(a+b*x)^(3/2)/(x)^(1/2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:875
        parse!("(a+b*x)/(x^2*(c*x^2)^(1/2))"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:1189
        parse!("(a+b*x)^2/(a*c-b*c*x)^6"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:1480
        parse!("(a+b*x)^3*(c+d*x)^10"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:1815
        parse!("(a+b*x)^(3/2)/(c+d*x)^(2/3)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.input:2108
        parse!("(c+d*x)^(13/6)/(a+b*x)^(7/6)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:253
        parse!("x^2*(A+B*x)/(a+b*x)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:560
        parse!("x*(A+B*x)/(a+b*x)^(3/2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:866
        parse!("x^2*(c+d*x)^(1/2)/(a+b*x)^(1/2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:1177
        parse!("(a+b*x)^n*(c+d*x)^p"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:1459
        parse!("(1-2*x)*(2+3*x)^7/(3+5*x)^3"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:1736
        parse!("(3+5*x)^3/((1-2*x)*(2+3*x)^8)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:2022
        parse!("(A+B*x)*(d+e*x)^(1/2)/(a+b*x)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:2307
        parse!("(3+5*x)/(1-2*x)^(1/2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:2595
        parse!("(1-2*x)^(1/2)*(3+5*x)^(1/2)/(2+3*x)^2"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:2880
        parse!("(2+3*x)^4*(3+5*x)^(3/2)/(1-2*x)^(3/2)"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:3172
        parse!("(1-2*x)^(5/2)/((2+3*x)^(5/2)*(3+5*x)^(1/2))"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.input:3489
        parse!("(a+b*x)*(c+d*x)^(-5+n)/(e+f*x)^n"),
        // 1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.input:164
        parse!("x^3*(e+f*x)^n/((a+b*x)*(c+d*x))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.2 (c x)^m (a+b x^2)^p.input:79
        parse!("(a+b*x^2)^5/x^19"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.2 (c x)^m (a+b x^2)^p.input:391
        parse!("x*(a+b*x^2)^(1/2)"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.2 (c x)^m (a+b x^2)^p.input:660
        parse!("1/((c*x)^(1/2)*(a+b*x^2)^(1/2))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.2 (c x)^m (a+b x^2)^p.input:948
        parse!("x^2/(2+3*x^2)^(3/4)"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.3 (a+b x^2)^p (c+d x^2)^q.input:173
        parse!("(3-x)/((1-x^2)^(1/3)*(3+x^2))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.4 (e x)^m (a+b x^2)^p (c+d x^2)^q.input:73
        parse!("x^2*(A+B*x^2)/(a+b*x^2)"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.4 (e x)^m (a+b x^2)^p (c+d x^2)^q.input:361
        parse!("x^m*(A+B*x^2)/(a+b*x^2)"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.4 (e x)^m (a+b x^2)^p (c+d x^2)^q.input:660
        parse!("(A+B*x^2)/(x^8*(a+b*x^2)^(3/2))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.4 (e x)^m (a+b x^2)^p (c+d x^2)^q.input:960
        parse!("(a+b*x^2)^2/((e*x)^(7/2)*(c+d*x^2)^(1/2))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.4 (e x)^m (a+b x^2)^p (c+d x^2)^q.input:1299
        parse!("(c+d*x^2)/((e*x)^(1/2)*(a+b*x^2)^(5/4))"),
        // 1.1 Binomial products/1.1.2 Quadratic/1.1.2.8 P(x) (c x)^m (a+b x^2)^p.input:71
        parse!("(-1+x^2)/(1+x^2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:172
        parse!("(b*x^n)^(1/2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:462
        parse!("x^3*(a+b*x^3)^(3/2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:747
        parse!("1/(x^2*(a+c*x^4))"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:1023
        parse!("x^7/(1+x^4)^(1/2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:1298
        parse!("x^3*(a-b*x^4)^(1/4)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:1624
        parse!("x^m/(a+b*x^7)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:1989
        parse!("(a+b/x)^(3/2)*x^2"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:2279
        parse!("(a+b/x^2)^p*(c*x)^m"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:2616
        parse!("x^3/(a+b*(x)^(1/2))^8"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:3026
        parse!("x*(a+b*x^n)^(1/2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:3321
        parse!("x^m*(a+b*x^(2+2*m))^(1/2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.input:3707
        parse!("1/(x*(a+b*(c*x^n)^(1/n)))"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.input:254
        parse!("(a+b*x^4)^(7/4)/(c+d*x^4)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.input:83
        parse!("(A+B*x^3)/(x^8*(a+b*x^3))"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.input:378
        parse!("1/(x^7*(8*c-d*x^3)*(c+d*x^3)^(3/2))"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.input:682
        parse!("x^6*(a+b*x^3)^(2/3)/(a*d-b*d*x^3)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.input:997
        parse!("x^11/((a+b*x^6)*(c+d*x^6)^(1/2))"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.input:50
        parse!("(e*x)^m*(A+B*x^n)/((a+b*x^n)^3*(c+d*x^n)^2)"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p.input:387
        parse!("x^14*(c+d*x^3+e*x^6+f*x^9)/(a+b*x^3)^3"),
        // 1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p.input:695
        parse!("(c+d*x+e*x^2+f*x^3)/(x^5*(a+b*x^4)^(1/2))"),
        // 1.1 Binomial products/1.1.4 Improper/1.1.4.2 (c x)^m (a x^j+b x^n)^p.input:281
        parse!("a*x^2+b*x^3"),
        // 1.1 Binomial products/1.1.4 Improper/1.1.4.3 (e x)^m (a x^j+b x^k)^p (c+d x^n)^q.input:24
        parse!("(A+B*x^2)*(b*x^2+c*x^4)^2/x"),
        // 1.1 Binomial products/1.1.4 Improper/1.1.4.3 (e x)^m (a x^j+b x^k)^p (c+d x^n)^q.input:309
        parse!("x^m*(A+B*x^2)*(b*x^2+c*x^4)^p"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:114
        parse!("x^(5/2)/(b*x+c*x^2)^(1/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:419
        parse!("(d+e*x)^(1/2)*(b*x+c*x^2)^3"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:717
        parse!("(d+e*x)^(5/2)/(a+c*x^2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:1016
        parse!("(d+e*x)^(7/2)/(c*d^2-c*e^2*x^2)^(1/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:1320
        parse!("(b*d+2*c*d*x)*(a+b*x+c*x^2)^3"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:1601
        parse!("(c*e+d*e*x)^(3/2)/(1-c^2-2*c*d*x-d^2*x^2)^(1/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:1889
        parse!("(d+e*x)^(15/2)/(a^2+2*a*b*x+b^2*x^2)^3"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:2178
        parse!("(a*d*e+(c*d^2+a*e^2)*x+c*d*e*x^2)^(3/2)/(d+e*x)^3"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:2482
        parse!("1/((d+e*x)*(a+b*x+c*x^2))"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.input:2763
        parse!("(d+e*x)^(1/2)*(a+b*x+c*x^2)^(3/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:139
        parse!("x^4*(A+B*x)/(b*x+c*x^2)^(3/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:428
        parse!("(A+B*x)/(x^3*(a+c*x^2)^(5/2))"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:716
        parse!("x^6*(A+B*x)/(a^2+2*a*b*x+b^2*x^2)^3"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:1005
        parse!("(3+2*x)/(13+12*x+4*x^2)^2"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:1305
        parse!("(A+B*x)*(b*x+c*x^2)^(1/2)/(d+e*x)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:1594
        parse!("(5-x)/((3+2*x)^3*(2+3*x^2)^(5/2))"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:1910
        parse!("(A+B*x)*(a^2+2*a*b*x+b^2*x^2)^2/(d+e*x)^9"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:2203
        parse!("(a+b*x)/((d+e*x)*(a^2+2*a*b*x+b^2*x^2)^3)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:2513
        parse!("(f+g*x)/((d+e*x)*(c*d^2-b*d*e-b*e^2*x-c*e^2*x^2)^(1/2))"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.input:2824
        parse!("(A+B*x)*(d+e*x)^3/(a+b*x+c*x^2)^(3/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.input:202
        parse!("(d^2-e^2*x^2)^(5/2)/(x^5*(d+e*x)^2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.input:534
        parse!("(a+b*x^2)^p/(x^2*(d+e*x)^3)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.input:891
        parse!("(f+g*x)^3*(a*d*e+(c*d^2+a*e^2)*x+c*d*e*x^2)^(3/2)/(d+e*x)^(3/2)"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q.input:51
        parse!("(3-x+2*x^2)/(2+3*x+5*x^2)^2"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.9 P(x) (d+e x)^m (a+b x+c x^2)^p.input:28
        parse!("(A+B*x+C*x^2)/((d+e*x)^2*(d^2-e^2*x^2)^(1/2))"),
        // 1.2 Trinomial products/1.2.1 Quadratic/1.2.1.9 P(x) (d+e x)^m (a+b x+c x^2)^p.input:354
        parse!(
            "(d+e*x+f*x^2)^p*(-2*c*e^2+2*c*d*f+3*b*e*f-c*e^2*p+2*b*e*f*p+2*b*f^2*(3+2*p)*x+2*c*f^2*(3+2*p)*x^2)"
        ),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.input:171
        parse!("(b*x^2+c*x^4)/x^2"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.input:453
        parse!("1/((b*x^2+c*x^4)^(3/2)*(x)^(1/2))"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.input:736
        parse!("1/(x^2*(a^2+2*a*b*x^2+b^2*x^4)^(1/3))"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.input:1026
        parse!("x*(a+b*x^2+c*x^4)^(1/2)"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^m (a+b x^2+c x^4)^p.input:87
        parse!("(1-2*x^2)/(1+3*x^2+4*x^4)"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^m (a+b x^2+c x^4)^p.input:443
        parse!("(2+x^2-x^4)^(1/2)"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.input:219
        parse!("(2+3*x^2)*(3+5*x^2+x^4)^(3/2)/x^6"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.5 P(x) (a+b x^2+c x^4)^p.input:28
        parse!("(d+e*x+f*x^2+g*x^3)/(1+x^2+x^4)"),
        // 1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p.input:59
        parse!("(A+B*x^2)/((d+e*x^2)^2*(a+b*x^2+c*x^4)^(1/2))"),
        // 1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.input:285
        parse!("x^2/(a+b*x^3+c*x^6)^(3/2)"),
        // 1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.input:676
        parse!("x^(-1-3*n)/(b*x^n+c*x^(2*n))"),
        // 1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.input:18
        parse!("(d+e*x^3)^5*(a+b*x^3+c*x^6)"),
        // 1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p.input:116
        parse!("x^11/(a*x+b*x^3+c*x^5)^2"),
        // 1.3 Miscellaneous/1.3.1 Rational functions.input:294
        parse!("(a+c*x^2)*(1+(d+a*x+1/3*c*x^3)^5)"),
        // 1.3 Miscellaneous/1.3.1 Rational functions.input:633
        parse!("(31+5*x)/(11-4*x+3*x^2)"),
        // 1.3 Miscellaneous/1.3.2 Algebraic functions.input:351
        parse!("(c*(a+b*x^2)^3)^(3/2)/x"),
        // 1.3 Miscellaneous/1.3.2 Algebraic functions.input:690
        parse!("(a+x^2)^(5/2)*(x-(a+x^2)^(1/2))^n"),
        // 1.3 Miscellaneous/1.3.2 Algebraic functions.input:1018
        parse!("(1+2*x)*(x+x^2)^3*(1-(x+x^2)^2)^(1/2)"),
        // 1.3 Miscellaneous/1.3.2 Algebraic functions.input:1359
        parse!("(1+4*x)/(9+120*x+64*x^2+64*x^3+64*x^4)^(1/2)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
