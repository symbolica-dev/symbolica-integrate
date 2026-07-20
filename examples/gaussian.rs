use symbolica::prelude::*;
use symbolica_integrate::Integrate;

fn main() {
    let x = symbol!("x");
    let integrand = parse!("cos(a*x)*sin(b*x)");
    let primitive = integrand
        .integrate(x)
        .expect("the Gaussian integral should produce erf");

    println!("Integral of {integrand} with respect to x:");
    println!("{primitive}");

    let residual = (primitive.derivative(x) - integrand).expand();
    assert!(residual.is_zero());
}
