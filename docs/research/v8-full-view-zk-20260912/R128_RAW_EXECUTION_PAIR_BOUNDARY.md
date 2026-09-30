# R128: raw execution and circle-pair prefix boundary

Source base: `c37c2c9675ad342db88a38e5430d39cecfd32119`.

Two focused R19 leaves compiled on the pinned NUC overlay. The raw execution
bridge proves deterministic equality through read, limb, four-limb, and
challenge recursion under `stateRawEquiv`. The circle-pair prefix proves the
exact first-circle → absorb0 → three-attempt distinct-second → absorb1
evaluation/run, with both inner and exhaustion error branches preventing later
absorbs.

The replay used Lean 4.32.0 with `-j1 -M4500` in a 5G/7G zero-swap scope.
There are five clean theorem audits; the dependency set is the 272-entry R122
overlay pin set.

## Explicitly open

The independent-uniform `State` answers have not been replaced with a
flat/raw-attempt distribution, and advance ghosts have not yet been retained
in that distributional bridge. Actual Rust callback equivalence, freshness or
loss, privacy, and soundness remain open.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r128_evidence.py
```
