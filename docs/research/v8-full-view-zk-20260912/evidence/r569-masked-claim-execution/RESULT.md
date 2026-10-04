# R569 actual masked-claim source translation and Lean audit

This record covers a focused translation and compilation of the actual selected `begin_state_only_masked_sumcheck` implementation and its reachable transcript/field helpers. It does not prove that changing the absorbed claim produces a distinct transcript challenge, nor does it establish privacy or security.

## Source and translation

- Frozen selected source revision: `6677d5f1310ff7373301fbd79f186278f772e68a`.
- Capture-stage repository head: `95261201338bfba305516455f07bfb55d014f17d`; the stage appended only a host-side `claim_probe` wrapper while retaining the selected core source files unchanged.
- Exact LLBC: `R569MaskedClaimCompleteConsts.llbc`, SHA-256 `a40beff355e21359851b01e9e1f53d86d244e302a80e740a02c87645534bed52`.
- Charon capture: exit 0; no LLBC errors; generic Option remains generic; default constant mode. The selected wrapper, its `From<ChallengeSampleExhausted>` conversion, and the two selected source constant initializers are structured bodies.
- Aeneas: pinned binary SHA-256 `e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813`; translation exit 0. Generated raw Funs SHA-256 `76fdc41e055509da697a29b8a14541ed65142e019649ea2dc32e27349de84f5d`; raw Types SHA-256 `af6114fc5a59fdf1b5834cb4b1acaf72b028a83f2d09097b790e0a1972dda015`.

## Import-only Lean adaptation and focused compile

The generated files import top-level `Aeneas`, which is absent from the pinned cache. The sole source adaptation replaces that import with the three already-cached imports `Aeneas.Std`, `Aeneas.Data.Discriminant`, and `Aeneas.Tactic.RustAttributes`. The exact diff is `R569-import-only-adaptation.patch`; no declarations or generated bodies changed.

- Adapted Types SHA-256 `85ff402093c35080aa1b5ff58c577bd461e99b4c2ac9a0833ec5f7906d13e66d`; exit 0, wall 1.00 s, peak RSS 2,543,744 KiB, swap 0.
- Adapted Funs SHA-256 `23f95e37f92a525c6d24392048d77953cc7dd47cf455ad48dcb5124a55fb13a6`; exit 0, wall 1.60 s, peak RSS 2,562,740 KiB, swap 0.
- Both used Lean 4.32.0 with `-j1 -M4500`, cached dependencies only, each in its own systemd scope at MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128.
- Oleans: Types `b226603b0b4971fbbeb11dd35be900817811ba52768e572029d310af4e71bbae`; Funs `219cf1d7522d47ffce1b0282d187bb26b9243b3b7150a68b242eea1e92a155de`.

## Axiom audit

`Axioms.lean` issues `#print axioms` for all 20 generated function rows, 12 generated global rows, and 6 generated type rows (38 unique declarations). Exit 0; wall 0.96 s; peak RSS 2,544,576 KiB; swap 0. Complete output is in `R569-Axioms.compile.log`.

The generated transcript challenge/nonzero loops, `begin_state_only_masked_sumcheck`, and the host-only probe depend on `propext`, `Classical.choice`, `Quot.sound`, and `Aeneas.Std.core.fmt.Formatter`. Field byte writers and transcript absorb report `propext`, `Classical.choice`, and `Quot.sound`. Other declarations report either those standard axioms or no axioms. No project-specific `sorryAx`, `admit`, or custom source axiom appears.

## Precise boundary

The generated function bodies compile and their axiom dependencies are recorded. The host-only `claim_probe` is not part of the selected verifier. This result does not prove native memory adequacy, byte-level claim serialization injectivity, distinct transcript addresses for distinct claims, challenge freshness, shared-oracle behavior, a simulator, probability loss, or an end-to-end privacy/security theorem. Those remain open.
