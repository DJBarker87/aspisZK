# R592: finite block execution

R592 connects finite four-block execution with indexed block replies and the 32-word tape. It also shows that the independent block-output observation law equals the mean of the sequential-word result observation.

## Verification

- Canonical source: `lean/AspisV8R19/R592FiniteBlockExecution.lean`
- Original draft: `.r21-scratch/R592FiniteBlockExecution.UNVERIFIED.lean`
- Canonical/draft SHA256: `1a66becfca17d199af96be1b41f58ffe45de8fb7f5d336b3b98f9faae951d74e` (byte-identical)
- Final canonical target receipt: `1791088859163766000`
- Source revision: `d3fe1380628dad8ebd1373fc60fc2f0193c8e31a`
- Result: exit 0; wall 1.35 s; Lean-child peak RSS 3,263,060 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Five complete final `#print axioms` reports use only subsets of `[propext, Classical.choice, Quot.sound]`.

The evidence preserves both earlier focused failures: `1791088797247704000` (State ambiguity and observer shape) and `1791088826871019000` (`blockWord` was not unfolded), together with their source snapshots, logs, receipts, and complete axiom output. The final source, direct pins, runner, publish paths, and SHA manifest are in `evidence/r592-finite-block-execution/`. No check was rerun for this promotion.

## Boundary

R592 proves deterministic finite four-block execution against indexed replies and the 32-word tape, plus the stated independent block output law. It preserves rejection, failure, stopping, cached-block, and reply-counter behavior through those abstract programs.

It does not prove the ordered joint tuple law, actual shared-oracle losses, or the admissible circle conditional law; it proves no privacy or security theorem. The next required step is the exact joint ordered tuple law through R579/R593, then actual shared-oracle loss and admissible-circle conditional arguments.
