use symbolica::prelude::*;
use symbolica_integrate::Integrate;

fn main() {
    let x = symbol!("x");
    let integrand = parse!("exp(a*x)*sin(b*x)");
    let primitive = integrand
        .integrate(x)
        .expect("the exponential-trigonometric product should integrate");

    println!("Integral of {integrand} with respect to x:");
    println!("{primitive}");

    let residual = (primitive.derivative(x) - integrand).expand().together();
    assert!(residual.is_zero());
}
