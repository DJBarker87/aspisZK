# R587: block sampler bound

R587 supplies the structural finite-tape certificate `Within challengeBlockProgram 4` for R584’s independent block sampler. `Within` is Type-valued, so the certificate is a definition rather than a proposition theorem.

The proof follows the exact rollover recurrence. It counts the one block ask at index 8 and no ask at other reads, preserves both rejection recursion and accepting stop branches, uses `rolloverCount_eight_le_one` for each eight-draw limb, proves the initial index-zero limb has zero asks, and composes the remaining three limbs. The initial block ask plus the initial zero-ask limb plus the three bounded tail limbs gives four.

## Verification

- Canonical source: `lean/AspisV8R19/R587BlockSamplerBound.lean`
- Original draft: `.r21-scratch/R587BlockSamplerBound.UNVERIFIED.lean`
- Canonical/draft SHA256: `699f8e7cdd31c1e30eba90afb86c3e6b0c1ecfcc118b984c4a4bbefe6254dd0e` (byte-identical)
- Canonical target receipt: `1791087600911564000`
- Source revision: `9cec79766c6977ae93e2b2bc458532b9b6888611`
- Result: exit 0; wall 1.33 s; Lean-child peak RSS 3,260,124 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Complete final `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

All seven failed focused attempts and two saved green attempts, with exact source snapshots, logs, receipts, runner, three direct dependency source copies, publish-path JSON, and recursive SHA manifest, are retained in `evidence/r587-block-sampler-bound/`. No unchanged job was rerun for this promotion.

## Boundary

R587 is a structural all-branches bound for the independent `BlockProgram`; it preserves rejection and stopping. It does not couple the finite four-block tape to the actual `BlockProgram`, establish a shared-oracle law, prove privacy, or prove security.

The first remaining proposition is finite four-block tape to actual `BlockProgram` coupling, followed by the shared-oracle law.
