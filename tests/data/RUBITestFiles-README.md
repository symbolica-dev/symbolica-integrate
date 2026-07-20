# Rubi Test Corpus

`RUBITestFiles/` comes directly from Rubi's official Axiom-syntax test-suite
archive:

<https://rulebasedintegration.org/TestFiles/AxiomSyntaxFiles/AxiomSyntaxTestFiles.zip>

The archive was downloaded on 2026-07-19. Its SHA-256 digest was
`d9debdd24ada7f6c6aa7c87bde75f61c9bbbe5083a127dfb75f1fc9469c66653`.
Rubi publishes the available test-suite translations on its
[Integration Test Problems](https://rulebasedintegration.org/testProblems.html)
page.

The corpus contains 213 Axiom `.input` files. Each integration case is a
single line beginning with `[`, whose first top-level field is the integrand
and whose second field is the integration variable. `tests/rubi_corpus.rs`
integrates the first field with respect to the second. It also inspects the
reference primitive to classify unsupported functions and cases that Rubi
itself leaves unintegrated; it does not compare antiderivative expression
forms or scores.

Rubi is licensed under MIT. Its license text is retained in the adjacent
`Rubi-LICENSE` file.

Run the full corpus harness with:

```bash
cargo test --test rubi_corpus -- --ignored
```

Useful corpus flags:

- `RUBI_SAMPLE=N` tests only every `N`th case.
- `RUBI_SKIP_RATIONAL=1` skips purely rational inputs that can spend a long
  time in the Trager/rational backend.
- `RUBI_INCLUDE_UNKNOWN_FUNCTIONS=1` includes cases whose Rubi reference
  primitive uses functions that Symbolica does not expose as public built-ins.

Every selected source case is parsed and handed to `symbolica-integrate`. The
harness requires a non-opaque primitive, differentiates it, and checks that the
residual is zero using exact normalization with a numeric fallback for standard
analytic identities. Unsupported cases, opaque `rootsum` results, Symbolica's
indeterminate sentinel, panics, and residuals it cannot prove zero fail the
test. The failure reports the first ten source locations; the current port is
expected to have failures because its Rubi coverage is intentionally partial.
