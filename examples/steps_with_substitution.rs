use symbolica::prelude::*;
use symbolica_integrate::Integrate;

fn main() {
    let x = symbol!("x");
    let explanation = parse!("exp(x)/(1+exp(x))").integrate_with_steps(x);

    println!("{}\n", explanation);
}
