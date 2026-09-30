# R129: independent-answer transport and arbitrary-history OOD pair law

Source base: `4ad6c579f47a4433b9c291b2efd4eac028dbf84b`.

Two focused R19 leaves compiled on the pinned NUC overlay. `IndependentAnswerTransport`
proves the exact reparameterization of already-independent `State` answers
through `stateRawEquiv`. `CirclePairHistoryLaw` proves the exact arbitrary-history
memoized law for the complete OOD-pair program; its reduction to `independentMean`
is conditional on the explicit branch-wise `FreshFrom` premise.

The replay used Lean 4.32.0 with `-j1 -M4500` in a 5G/7G zero-swap scope.
There are six clean theorem audits; the dependency set is the 272-entry R122
overlay pin set.

## Explicitly open

Prefix `FreshFrom` or an explicit collision-loss bound remains open. The raw
answers must still be flattened with retained advance ghosts into the
conditional accepted OOD law, and actual Rust callback equivalence remains
unproved. Privacy and soundness are not claimed.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r129_evidence.py
```
