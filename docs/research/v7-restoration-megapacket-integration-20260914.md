# V7 restoration megapacket integration

**Base:** `55653f25`  
**Source-normalisation milestone:** `c4088e38`

## Checked results

The indexed `WeightAccumulator::weight_at` normalisation was applied after
reviewing its exact patch.  It preserves the old shorter-zip line-batch rule
and leaves the terminal `dot` source untouched.

Focused capped Rust checks on `nuc.local` using `nightly-2026-06-01` and one
cargo job passed:

- the 13-test normalisation differential target, debug and release;
- the existing 7-test full-width observer target, debug and release.

The normalised real `weight_at` was then extracted by pinned Charon:

```text
V7WeightAtNormalized.llbc
SHA-256 5d5fd106825a761396df91d8b92b191c11c84da1886267e92f1bcad145d4f104
```

Pinned Aeneas translation of that LLBC completed successfully in the
`V7WeightAtNormalized` namespace under a `MemoryHigh=5G`, `MemoryMax=6G`,
zero-swap scope.  This removes the prior context-matching error at the
multilinear iterator path.  The generated output still requires a source
reflection proof and must not be treated as that proof.

`AspisK1.V7Tag73FiniteSubkernel` is the first inherited packet Lean leaf
compiled in the cached Lean 4.32 workspace, within `MemoryHigh=1500M`,
`MemoryMax=2G`, zero swap.  Its audited results use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Open work

The remaining predecessor leaves and all megapacket leaves still need
compilation in a coherent current cached workspace.  In particular no actual
restoration-wide K1.3/K1.4/K1.5 measure inequality has been instantiated.
The next source task is proving the generated indexed-helper and full
256-entry observer reflection, rather than importing generated templates.
Selected-build SBF/CU measurement is also required before treating the shared
`sumcheck.rs` change as release-ready.
