# R593: decoded tuple observation

R593 proves that the decoded-list equality indicator used by the source-shaped word observation is exactly `R572SequentialWordMass.observedList`. The result is generic in the finite element bound and preserves `none` as an observation outcome.

## Verification

- Canonical source: `lean/AspisV8R19/R593DecodedTupleObservation.lean`
- Original draft: `.r21-scratch/R593DecodedTupleObservation.UNVERIFIED.lean`
- Canonical/draft SHA256: `edb42935064139a2b28c332d703dd5870d68d9d5eb6ebfc9b17e6618078b8673` (byte-identical)
- Canonical target receipt: `1791088771173351000`
- Source revision: `d3fe1380628dad8ebd1373fc60fc2f0193c8e31a`
- Result: exit 0; wall 1.28 s; Lean-child peak RSS 3,252,980 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Complete `#print axioms` report: `[propext, Quot.sound]`.

The exact source, focused log and receipt, direct dependency source pins, runner, explicit publish paths, and SHA manifest are retained in `evidence/r593-decoded-tuple-observation/`. No check was rerun for this promotion.

## Boundary

The proof is deterministic representation plumbing. It proves the equality of two list-observation indicators by deriving injectivity of `List.map Fin.val`; it assumes neither successful sampling nor a fixed list length.

It does not prove a source execution correspondence, an oracle law, a shared-oracle probability bound, privacy, or security. The next required work remains the finite four-block tape bridge and transfer to actual shared-oracle losses.
