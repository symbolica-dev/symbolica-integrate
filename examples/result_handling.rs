use symbolica::prelude::*;
use symbolica_integrate::Integrate;

fn main() {
    let x = symbol!("x");
    let integrand = parse!("x+sin(x^x)");

    match integrand.integrate(x) {
        Ok(_) => unreachable!(),
        Err(deferred) => {
            println!("Deferred result: {deferred}");
        }
    }
}
