# Source terminal-weight construction

`lean/SameBodySourceTerminalWeight.lean` removes the arbitrary 256-entry
terminal covector from the functional relation producer.  The dense reference
is constructed from the selected inactive-row table, the three repaired
point-row MLE weights, the proved chord transpose, the sparse image gate and
the actual first relation challenge.  `completeDense` therefore retains only
the legal causal relation strategy and its realised same-word equality as a
caller interface.

This is a mathematical dense reference, not the optimized implementation.
The selected structured Rust contraction still needs an exact refinement to
this reference, including its frozen grouped-mask constants.  Likewise, the
new definition does not construct the causal strategy from the Rust parser or
Fiat--Shamir history.

The first two NUC attempts exposed incomplete mixed cache roots (missing
`V7PairForestCuArithmeticEquivalences.olean`, then
`V7Tag73VariablePrefixGammaSampler.olean`) and exited 1 before elaborating the
leaf.  The successful focused run used a private union of the pinned base and
V8 overlay artifacts, plus the already recorded first-party leaf artifacts;
it did not rebuild that imported closure.

## Focused evidence

- Base revision: `7e5e7bcbb33de272f9b83afa976da0f3878f45cf`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.05 seconds
- Peak RSS: 6,770,252 KiB
- Swap: 0
- Source SHA-256: `3dc345d4d4d90ca49c4f4c80daf036617f4e4999e47b0c22d7ef956dc66e590d`
- Olean SHA-256: `40752fad8e0da16a57780cb7683c71862d037a9ce5a07dc10c590229752d6d7b`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Dependency rebuild: not run; pinned artifacts were reused.
