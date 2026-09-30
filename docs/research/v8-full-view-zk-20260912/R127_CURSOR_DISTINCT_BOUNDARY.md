# R127: raw cursor and distinct-circle program boundary

Source base: `e5ad5468925e3a15b36a3347230b850e511f15d2`.

Two focused R19 leaves compiled on the pinned NUC overlay. `SamplerRawCursorBridge`
proves the deterministic one-read cursor representation, including the
before-rollover, rollover, and case decomposition. `DistinctCircleProgram`
proves the exact three-attempt distinct-second evaluation/run with inner and
exhaustion failures retained visibly.

The replay used Lean 4.32.0 with `-j1 -M4500` in a 5G/7G zero-swap scope.
There are four clean theorem audits; the dependency set is the 272-entry R122
overlay pin set.

## Explicitly open

Limb/whole-challenge raw-stream composition, actual callback equivalence,
freshness and source distribution remain open. No privacy or soundness claim
is made.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r127_evidence.py
```
