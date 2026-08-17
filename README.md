# Symbolica-integrate

<p align="center">
<a href="https://symbolica.io"><img alt="Symbolica website" src="https://img.shields.io/static/v1?label=symbolica&message=website&color=orange&style=flat-square"></a>
  <a href="https://zulip.symbolica.io"><img alt="Zulip Chat" src="https://img.shields.io/static/v1?label=zulip&message=discussions&color=blue&style=flat-square"></a>
    <a href="https://github.com/symbolica-dev/symbolica-integrate"><img alt="symbolica-integrate repository" src="https://img.shields.io/static/v1?label=github&message=development&color=green&style=flat-square&logo=github"></a>
    <a href="https://app.codecov.io/gh/symbolica-dev/symbolica-integrate"><img alt="Codecov" src="https://img.shields.io/codecov/c/github/symbolica-dev/symbolica-integrate?token=W5GTATIVZI&style=flat-square"></a>
</p>

Rule-based symbolic integration for [Symbolica](https://symbolica.io/), based on
the 7000+ [Rubi](https://rulebasedintegration.org/) integration rules.


## Usage

```rust
use symbolica_integrate::Integrate;
use symbolica::prelude::*;

let x = symbol!("x");
let integrand = parse!("cos(a*x)*sin(b*x)");
let primitive = integrand
    .integrate(x)
    .unwrap();
println!("{primitive}");
```
```
1/2*cos(x*(-a+b))/(a-b)-1/2*cos(x*(a+b))/(a+b)
```


### Integration steps

Enable the `steps` feature to retain Rubi's rule sources and short
transformation descriptions, and use `integrate_with_steps` to obtain an
outer-to-inner derivation:

```rust
use symbolica::prelude::*;
use symbolica_integrate::Integrate;

let steps = parse!("x/(x+1)").integrate_with_steps(symbol!("x"));
println!("{explanation}");
```

```log
∫ x/(1+x) dx = ∫ 1-1/(1+x) dx
  ∫ 1-1/(1+x) dx = ∫ 1 dx+∫ 1/(-1-x) dx
      ∫ 1 dx = x
      ∫ -1/(1+x) dx = -log(1+x)
  = x-log(1+x)
```

## Verification and timings

`symbolica-integrate` passes the complete 72,944-problem corpus. It takes 18 minutes of wall time, on a Ryzen 9 5900X with 8 cores. The measured time per problem had
a **57 ms median**, **118 ms average**, and **10.8 s maximum**.

These timings are competitive, as an integration run on the independent test suite consisting of 1,892 problems shows:

| Integrator                        |     Time |
| --------------------------------- | -------: |
| `symbolica-integrate`             | 111.24 s |
| Rubi 4.17.3.0 in Mathematica 13.2 | 155.78 s |
| Symja `Integrate` 3.3.0 [^1] | ≥ 1,316.02 s |

In these runs, `symbolica-integrate` was **1.40× faster** than Rubi in
Mathematica and at least **11.83× faster** than Symja.

[^1]: Symja timed out on 18 problems.

## Acknowledgements

Rubi was created by Albert D. Rich and is currently maintained by Patrick Scheibe and others. See the [Rubi website](https://rulebasedintegration.org/about.html) for more information.

This port aims to preserve Rubi's 7000+ rule ordering and integration routes while using Symbolica's
native expression and pattern-matching infrastructure.

## License

`symbolica-integrate` is released under the [MIT License](LICENSE). It depends
on Symbolica, which is distributed under [separate licensing
terms](https://symbolica.io/license/).
