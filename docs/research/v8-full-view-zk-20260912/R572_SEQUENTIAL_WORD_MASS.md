# R572: exact output mass for the sequential independent-word model

The focused Lean target proves the probability of one ordered successful output tuple for an abstract finite word-ask program. The ask answers are independent uniform `Option (Fin p)` values, and every limb shares a monotonically advanced cursor. This is a word-level probability lemma only; it is not a law for the selected Rust challenge sampler.

For `p > 0`, scan budget `n`, limb count `k`, any starting cursor, and any target tuple `target : Fin k → Fin p`, the theorem
`AspisV8R19.R572SequentialWordMass.limbs_exact_mass` proves:

```lean
independentMean (limbs budget count cursor)
  (observedList (List.ofFn target))
  = ((1 - (1 / (p + 1 : ℚ)) ^ budget) / p) ^ count
```

The observer gives weight 1 only to the exact successful ordered output list. The program itself retains `none` failures and the final cursor on both success and failure. This theorem does not establish the joint distribution of that final cursor: the observer ignores it. Instantiating `p = 2147483647`, `budget = 8`, and `count = 4` is an algebraic specialization of this model, not a source-sampler probability claim.

The first remaining source obligation is to refine the actual 32-byte block and shared word cursor to this independent word-ask program, including block advance calls, unused-tail handling and actual returned cursor/state. The actual lazy shared-oracle law still needs unread-address/collision treatment over adaptive history, including bounded retries and stopping. No privacy, soundness, security, or 100-bit claim follows from R572.

## Verification record

- Exact target: `AspisV8R19/R572SequentialWordMass.lean`.
- Source revision: `95261201338bfba305516455f07bfb55d014f17d`.
- Source SHA-256: `cb40bdb40b9ebd4a15ca7c8f96c8e114f9f5e2dd11cf730dfd32986696f12e46`.
- Focused pinned Lean 4.32 cached-host run: exit 0; wall 1.73 s; peak Lean-child RSS 3,256,472 KiB; swap 0; `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; flags `-j1 -M4500`.
- Final run identifier: `1791081897975744000`.
- Complete axiom outputs for `scanMass_cursor`, `scanMass_step`, `scanMass_value`, and `limbs_exact_mass`: each reports `[propext, Classical.choice, Quot.sound]`.
- Direct import SHA-256 pins: `AdaptiveFirstReadLaw` `1d1eddc27b49351d26aa78bc9065b33b597ccd0517d6cde7269be7a578902e0a`; `R443BoundedRejectionMass` `154a7918b007ea19879f057f3b4bebb902538235cd96814b746d99aeb518b635`.

Seven earlier focused attempts failed during elaboration and are retained alongside the final successful attempt. No memory cap was raised, no package replay was run, and no verifier source or benchmark was changed. The exact Lean source, runner, logs, receipts, and source snapshots are in [the R572 evidence bundle](evidence/r572-sequential-word-mass/).
