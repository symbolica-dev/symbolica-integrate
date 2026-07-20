// Generated from tests/data/RUBITestFiles by the corpus section sampler.
// Section: 4 Trig functions. Deterministic, evenly spaced source cases.

use symbolica::prelude::*;
use symbolica_integrate::Integrate;

#[test]
fn corpus_samples_4_trig() {
    let samples = [
        // 4.1 Sine/4.1.0 (a sin)^m (b trg)^n.input:10
        parse!("sin(a+b*x)"),
        // 4.1 Sine/4.1.0 (a sin)^m (b trg)^n.input:261
        parse!("(d*cos(a+b*x))^(1/2)*csc(a+b*x)"),
        // 4.1 Sine/4.1.0 (a sin)^m (b trg)^n.input:529
        parse!("(a*sin(e+f*x))^(1/2)*(b*sec(e+f*x))^(1/2)"),
        // 4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.input:81
        parse!("cos(c+d*x)^2/(a+a*sin(c+d*x))^2"),
        // 4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.input:322
        parse!("(a+a*sin(c+d*x))^(5/2)/(e*cos(c+d*x))^(5/2)"),
        // 4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.input:570
        parse!("sec(c+d*x)/(a+b*sin(c+d*x))^(3/2)"),
        // 4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.input:109
        parse!("(a+a*sin(e+f*x))^(1/2)*tan(e+f*x)^2"),
        // 4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.input:275
        parse!("csc(c+d*x)/(a+a*sin(c+d*x))"),
        // 4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.input:458
        parse!("(e+f*x)*cos(c+d*x)^3*cot(c+d*x)/(a+b*sin(c+d*x))"),
        // 4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.input:129
        parse!("(e*x)^m*(a+b*sin(c+d*x^3))"),
        // 4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.input:441
        parse!("x^m*(c*sin(a+b*x^n)^3)^(1/3)"),
        // 4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.input:201
        parse!("sin(e+f*x)^2*(a+b*sin(e+f*x))^2"),
        // 4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.input:465
        parse!("(c-c*sin(e+f*x))^(3/2)/(a+a*sin(e+f*x))^(1/2)"),
        // 4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.input:723
        parse!("(a+a*sin(e+f*x))^m"),
        // 4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.input:987
        parse!("(c*(d*sin(e+f*x))^p)^n/(a+b*sin(e+f*x))^2"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:277
        parse!("cos(c+d*x)*sin(c+d*x)^4/(a+a*sin(c+d*x))"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:547
        parse!("cos(c+d*x)^4*csc(c+d*x)^6*(a+a*sin(c+d*x))^(1/2)"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:809
        parse!("cos(c+d*x)^7*csc(c+d*x)^15*(a+a*sin(c+d*x))"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:1149
        parse!("sec(c+d*x)^9*sin(c+d*x)^5/(a+a*sin(c+d*x))"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:1444
        parse!("cos(c+d*x)^4*sin(c+d*x)^3/(a+b*sin(c+d*x))^2"),
        // 4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input:1720
        parse!("sec(c+d*x)^4*sin(c+d*x)^3/(a+b*sin(c+d*x))"),
        // 4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.input:39
        parse!("(a+a*sin(e+f*x))^(1/2)/((c-c*sin(e+f*x))*(g*sin(e+f*x))^(1/2))"),
        // 4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).input:154
        parse!("(A+B*sin(e+f*x))*(c-c*sin(e+f*x))^(9/2)/(a+a*sin(e+f*x))^3"),
        // 4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).input:411
        parse!("(a-a*sin(e+f*x))*(a+a*sin(e+f*x))^m*(c+d*sin(e+f*x))^n"),
        // 4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.input:206
        parse!("sin(e+f*x)^3/(a+b*sin(e+f*x)^2)^(5/2)"),
        // 4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.input:494
        parse!("cos(c+d*x)^2/(a+b*sin(c+d*x)^3)"),
        // 4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.input:35
        parse!("sec(x)/(a+b*sin(x)+c*sin(x)^2)"),
        // 4.2 Cosine/4.2.0 (a cos)^m (b trg)^n.input:263
        parse!("cos(c+d*x)*(b*cos(c+d*x))^(4/3)"),
        // 4.2 Cosine/4.2.1.2 (g sin)^p (a+b cos)^m.input:119
        parse!("1/((a+b*cos(c+d*x))^3*(e*sin(c+d*x))^(7/2))"),
        // 4.2 Cosine/4.2.13 (d+e x)^m cos(a+b x+c x^2)^n.input:13
        parse!("x^2*cos(a+b*x-c*x^2)"),
        // 4.2 Cosine/4.2.2.1 (a+b cos)^m (c+d cos)^n.input:227
        parse!("cos(c+d*x)^(5/2)*(a+a*cos(c+d*x))^(1/2)"),
        // 4.2 Cosine/4.2.2.1 (a+b cos)^m (c+d cos)^n.input:489
        parse!("(a+b*cos(c+d*x))^2*sec(c+d*x)^3"),
        // 4.2 Cosine/4.2.2.1 (a+b cos)^m (c+d cos)^n.input:734
        parse!("1/((3-2*cos(c+d*x))^(1/2)*(cos(c+d*x))^(1/2))"),
        // 4.2 Cosine/4.2.2.1 (a+b cos)^m (c+d cos)^n.input:1018
        parse!("cos(c+d*x)^(3/2)*(A+B*cos(c+d*x))/(b*cos(c+d*x))^(3/2)"),
        // 4.2 Cosine/4.2.3.1 (a+b cos)^m (c+d cos)^n (A+B cos).input:189
        parse!("(A+B*cos(c+d*x))/(cos(c+d*x)^(3/2)*(a+a*cos(c+d*x))^3)"),
        // 4.2 Cosine/4.2.3.1 (a+b cos)^m (c+d cos)^n (A+B cos).input:440
        parse!("cos(c+d*x)^(5/2)*(a*B+b*B*cos(c+d*x))/(a+b*cos(c+d*x))^2"),
        // 4.2 Cosine/4.2.3.1 (a+b cos)^m (c+d cos)^n (A+B cos).input:704
        parse!("(A+B*cos(c+d*x))*sec(c+d*x)^(5/2)/(a+b*cos(c+d*x))^(1/2)"),
        // 4.2 Cosine/4.2.4.1 (a+b cos)^m (A+B cos+C cos^2).input:236
        parse!("(b*cos(c+d*x))^n*(A+C*cos(c+d*x)^2)/cos(c+d*x)^(9/2)"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:41
        parse!("(a+a*cos(c+d*x))^4*(A+C*cos(c+d*x)^2)"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:294
        parse!("(B*cos(c+d*x)+C*cos(c+d*x)^2)/(a+a*cos(c+d*x))"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:558
        parse!("(A+B*cos(c+d*x)+C*cos(c+d*x)^2)*(a+a*cos(c+d*x))^(1/2)/cos(c+d*x)^(7/2)"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:808
        parse!("(A+C*cos(c+d*x)^2)*(cos(c+d*x))^(1/2)/(a+b*cos(c+d*x))"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:1070
        parse!("cos(c+d*x)^(3/2)*(B*cos(c+d*x)+C*cos(c+d*x)^2)/(a+b*cos(c+d*x))^(5/2)"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:1323
        parse!("cos(c+d*x)^m*(A+B*cos(c+d*x)+C*cos(c+d*x)^2)/(a+b*cos(c+d*x))"),
        // 4.2 Cosine/4.2.4.2 (a+b cos)^m (c+d cos)^n (A+B cos+C cos^2).input:1597
        parse!("(a+b*cos(c+d*x))^4*(A+C*cos(c+d*x)^2)*sec(c+d*x)^(11/2)"),
        // 4.2 Cosine/4.2.7 (d trig)^m (a+b (c cos)^n)^p.input:128
        parse!("cos(x)/(4-cos(x)^2)^(1/2)"),
        // 4.3 Tangent/4.3.0 (a trg)^m (b tan)^n.input:200
        parse!("(b*sin(e+f*x))^(1/2)/(d*tan(e+f*x))^(1/3)"),
        // 4.3 Tangent/4.3.0 (a trg)^m (b tan)^n.input:482
        parse!("cot(e+f*x)^2*(b*csc(e+f*x))^m"),
        // 4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.input:237
        parse!("(a+1i*a*tan(c+d*x))^4/(e*sec(c+d*x))^(11/2)"),
        // 4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.input:491
        parse!("(d*sec(e+f*x))^(2/3)*(a+1i*a*tan(e+f*x))^(2/3)"),
        // 4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.input:667
        parse!("(d*sec(e+f*x))^(5/2)/(a+b*tan(e+f*x))"),
        // 4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.input:59
        parse!("(c+d*x)^m/(a+1i*a*tan(e+f*x))^3"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:158
        parse!("(d*tan(e+f*x))^(5/2)*(a+1i*a*tan(e+f*x))"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:422
        parse!("1/((d*tan(e+f*x))^(1/2)*(a+a*tan(e+f*x)))"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:678
        parse!("1/((tan(c+d*x))^(1/2)*(a+b*tan(c+d*x)))"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:959
        parse!("(a+b*tan(c+d*x))^2/cot(c+d*x)^(5/2)"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:1219
        parse!("(a+1i*a*tan(e+f*x))^(1/2)/(c-1i*c*tan(e+f*x))^(5/2)"),
        // 4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.input:1487
        parse!("1/((a+b*tan(e+f*x))^2*(c+d*tan(e+f*x))^(5/2))"),
        // 4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).input:190
        parse!("tan(c+d*x)^(3/2)*(a+1i*a*tan(c+d*x))^(3/2)*(A+B*tan(c+d*x))"),
        // 4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).input:446
        parse!("(tan(c+d*x))^(1/2)*(a+b*tan(c+d*x))^2*(A+B*tan(c+d*x))"),
        // 4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).input:720
        parse!("cot(c+d*x)^(7/2)*(a+b*tan(c+d*x))^(1/2)*(A+B*tan(c+d*x))"),
        // 4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).input:972
        parse!("(c-1i*c*tan(e+f*x))^(1/2)*(A+B*tan(e+f*x))/(a+1i*a*tan(e+f*x))^(3/2)"),
        // 4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p.input:63
        parse!("sin(e+f*x)^2*(a+b*tan(e+f*x)^2)"),
        // 4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p.input:341
        parse!("cot(x)^4*(a+a*tan(x)^2)^(1/2)"),
        // 4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p.input:539
        parse!("(d*cot(e+f*x))^m*(a+b*tan(e+f*x)^2)^p"),
        // 4.4 Cotangent/4.4.2.1 (a+b cot)^m (c+d cot)^n.input:166
        parse!("(A+B*cot(c+d*x))/(a+b*cot(c+d*x))^(1/2)"),
        // 4.5 Secant/4.5.0 (a sec)^m (b trg)^n.input:160
        parse!("sec(c+d*x)^3/(b*sec(c+d*x))^(5/2)"),
        // 4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.input:64
        parse!("cos(c+d*x)^4/(a+a*sec(c+d*x))"),
        // 4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.input:318
        parse!("(e*sec(c+d*x))^(2/3)*(a+a*sec(c+d*x))^(1/2)"),
        // 4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.input:580
        parse!("cos(c+d*x)/(a+b*sec(c+d*x))^2"),
        // 4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.input:915
        parse!("cos(c+d*x)^(5/2)*(a+b*sec(c+d*x))"),
        // 4.5 Secant/4.5.1.3 (d sin)^n (a+b sec)^m.input:166
        parse!("(e*sin(c+d*x))^m/(a+a*sec(c+d*x))^(3/2)"),
        // 4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.input:76
        parse!("cot(c+d*x)^5/(a+a*sec(c+d*x))"),
        // 4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.input:331
        parse!("tan(c+d*x)^5/(a+b*sec(c+d*x))"),
        // 4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.input:111
        parse!("(c-c*sec(e+f*x))^(3/2)*(a+a*sec(e+f*x))^(1/2)"),
        // 4.5 Secant/4.5.2.3 (g sec)^p (a+b sec)^m (c+d sec)^n.input:90
        parse!("sec(e+f*x)*(a+a*sec(e+f*x))^2*(c-c*sec(e+f*x))^(3/2)"),
        // 4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).input:31
        parse!("sec(c+d*x)^2*(b*sec(c+d*x))^(4/3)*(A+B*sec(c+d*x))"),
        // 4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).input:291
        parse!("(a+a*sec(c+d*x))^(3/2)*(A+B*sec(c+d*x))/sec(c+d*x)^(9/2)"),
        // 4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).input:473
        parse!("(a+b*sec(c+d*x))*(A+B*sec(c+d*x))/sec(c+d*x)^(1/2)"),
        // 4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).input:741
        parse!("cos(c+d*x)^(3/2)*(A+B*sec(c+d*x))/(a+b*sec(c+d*x))^(3/2)"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:198
        parse!("cos(c+d*x)*(A+C*sec(c+d*x)^2)/(a+a*sec(c+d*x))^3"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:458
        parse!("cos(c+d*x)*(a+a*sec(c+d*x))^(3/2)*(B*sec(c+d*x)+C*sec(c+d*x)^2)"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:714
        parse!("sec(c+d*x)^(5/2)*(a+a*sec(c+d*x))^(5/2)*(A+B*sec(c+d*x)+C*sec(c+d*x)^2)"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:988
        parse!("sec(c+d*x)^3*(a+b*sec(c+d*x))^(3/2)*(B*sec(c+d*x)+C*sec(c+d*x)^2)"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:1253
        parse!("(a+b*sec(c+d*x))^(5/2)*(A+B*sec(c+d*x)+C*sec(c+d*x)^2)/(sec(c+d*x))^(1/2)"),
        // 4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).input:1525
        parse!("cos(c+d*x)^(7/2)*(A+B*sec(c+d*x)+C*sec(c+d*x)^2)/(a+a*sec(c+d*x))^(1/2)"),
        // 4.5 Secant/4.5.7 (d trig)^m (a+b (c sec)^n)^p.input:144
        parse!("sin(e+f*x)^6/(a+b*sec(e+f*x)^2)^(5/2)"),
        // 4.5 Secant/4.5.7 (d trig)^m (a+b (c sec)^n)^p.input:412
        parse!("tan(e+f*x)^3/(a+b*sec(e+f*x)^2)^2"),
        // 4.6 Cosecant/4.6.1.2 (d csc)^n (a+b csc)^m.input:73
        parse!("(a+b*csc(c+d*x))^4"),
        // 4.7 Miscellaneous/4.7.1 (c trig)^m (d trig)^n.input:137
        parse!("csc(a+b*x)^3*sin(2*a+2*b*x)^(3/2)"),
        // 4.7 Miscellaneous/4.7.2 trig^m (a trig+b trig)^n.input:117
        parse!("sec(c+d*x)^11*(a*cos(c+d*x)+b*sin(c+d*x))^4"),
        // 4.7 Miscellaneous/4.7.3 (c+d x)^m trig^n trig^p.input:33
        parse!("(c+d*x)^m*cos(a+b*x)*sin(a+b*x)^3"),
        // 4.7 Miscellaneous/4.7.3 (c+d x)^m trig^n trig^p.input:196
        parse!("(c+d*x)^2*cos(a+b*x)^3*sin(a+b*x)^3"),
        // 4.7 Miscellaneous/4.7.5 x^m trig(a+b log(c x^n))^p.input:84
        parse!("1/sin(a+b*log(c*x^n))^(5/2)"),
        // 4.7 Miscellaneous/4.7.5 x^m trig(a+b log(c x^n))^p.input:384
        parse!("csc(a+b*log(c*x^n))/x^2"),
        // 4.7 Miscellaneous/4.7.7 Trig functions.input:70
        parse!("cos(a+b*x)/(c+d*x+e*x^2)"),
        // 4.7 Miscellaneous/4.7.7 Trig functions.input:355
        parse!("1/(a*sec(x)+b*tan(x))^5"),
        // 4.7 Miscellaneous/4.7.7 Trig functions.input:636
        parse!("x^2/(a+b*cos(x)^2+c*sin(x)^2)"),
        // 4.7 Miscellaneous/4.7.7 Trig functions.input:942
        parse!("sec(x)*tan(x)/(a+b*sec(x))"),
        // 4.7 Miscellaneous/4.7.7 Trig functions.input:1218
        parse!("(-csc(a+b*x)^4+sec(a+b*x)^4)/(csc(a+b*x)^4+sec(a+b*x)^4)"),
    ];
    assert_eq!(samples.len(), 100);
    let x = symbol!("x");
    for integrand in samples {
        let _ = std::hint::black_box(integrand.integrate(x).unwrap());
    }
}
