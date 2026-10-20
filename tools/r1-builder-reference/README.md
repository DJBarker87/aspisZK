# Builder reference forms

This standalone crate is test/extraction-only. No shipped crate depends on it.
The Kani harness includes the actual shipped `transport.rs` by path and proves
S2's row function equals the arithmetic D18 formula for every `usize < 1024`,
plus its range and involution. It uses no function stubs. Unwind 6 covers both
five-iteration loops with unwinding assertions. The admitted size is fixed.

Run on the build host in an 8 GiB no-swap scope, with the host reservation
preflight, Kani 0.67.0:

```
cargo kani --manifest-path tools/r1-builder-reference/Cargo.toml -j 4 --output-format terse --harness s2_row_equals_d18
```

Kani reports its compiler profile as `dev`; this is verification compilation,
not an unoptimized arithmetic/proof-generation execution. The solver gate
finished in 0.214 seconds (4.98 seconds including compilation).

Evidence: `docs/research/v8-r0-zk-20261009/r1p-final/builder-d83-evidence/transport-kani.json`.
This is a named P6 tool-soundness dependency. It supplies neither a Lean
certificate nor the shipped compiler's records/glue identification.


The extracted arithmetic reference is kernel-refined to D18 in
`R1Z/BuilderTransport.lean` (env J 8452, standard axioms). The separate
`records.rs` module is included only under `cfg(kani)` in the statement
crate. It contains the unstubbed whole-mapper experiment and a parametric
shared-root experiment. Neither should be read as a completed source
certificate without checking `BUILDER-REFINEMENT-20261021.md` and the exact
Kani receipts. The shared-root experiment explicitly requires `-Z stubbing`;
its scope is all possible returns of the common pure helper. It proves
neither the helper's hash computation nor caller admission.
