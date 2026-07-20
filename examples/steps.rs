use symbolica::prelude::*;
use symbolica_integrate::Integrate;

fn main() {
    let x = symbol!("x");
    let explanation = parse!("x/(x+1)").integrate_with_steps(x);

    println!("{}\n", explanation);

    println!("Detailed rule walkthrough:");
    for step in &explanation.steps {
        let indent = "  ".repeat(step.depth);
        let source = step.source.replace('\n', &format!("\n{indent}  "));
        println!("{indent}{}", step.description);
        println!("{indent}  {} = {}", step.input, step.output);
        for reference in step.references {
            println!("{indent}  Reference: {reference}");
        }
        println!("{indent}  Source: {source}");
    }
}
