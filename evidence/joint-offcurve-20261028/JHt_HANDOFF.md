# Off-curve proof work

Stage 1: `JHt_ModPow.correct` proves binary modular exponentiation equals
`Nat.pow` modulo m, for arbitrary Nat inputs. One recursive occurrence per
exponent bit; bases reduced after each square. No huge ordinary power is
computed. Check JHt_002: exit 0, 1.507738701 seconds, peak 3,323,124 KiB,
swap 0; axioms propext and Quot.sound. JHt_001 was a rejected rewrite proof
(exit 1, 1.460076083 seconds, peak 3,307,412 KiB, swap 0); corrected before
retry. Exact revision, source hashes, commands and caps are in each receipt.

Own host cache was seeded by copying the assigned JHs cache (345 MiB).
Seed was read only; own cache retained. All scopes 6G/8G, swap 0, TasksMax64,
Lean -M7000. 2/30 Lean attempts used. Seven fixture facts remain open.

Stage 2: bounded structural modPow correctness, Lucas certificate bridge and
255-bit preflight passed (JHt_006 and JHt_008). `JHt_Prime` proves
2^255-19 prime with 53 Pratt nodes and separate checked residue theorems.
JHt_011: exit 0, 5.806709420 seconds, peak 3384368 KiB, swap 0. Standard axioms only.
Generator --check passes. Rejected earlier attempts are retained.
JHt_003 corrected an own LEAN_PATH ordering error: complete pinned Mathlib
precedes a partial same-version overlay; compared ModEq object hashes match.
JHt_004/005: well-founded executable would not reduce through tactics.
Replaced concrete computation with structural bit budget (JHt_006); original
symbolic theorem remains valid but unused by final arithmetic. JHt_007 hit
elaborator recursion depth; kernel evaluator JHt_008 passes without raising
limits. JHt_009 had a cast rewrite mismatch, JHt_010 accidental elaborator
unfolding. JHt_011 uses local irreducibility to keep rewrites symbolic and
`decide +kernel` only for one bounded exponentiation at a time.
11/30 Lean attempts used. Seven fixture facts still open.

## Completed claim and consumer

`lean/JHt_OffCurve.lean` proves the seven exact negations of
`JHs_PDA.OnCurve (decodeState key)` with no hypotheses:
`masterOffCurve`, `checkpointOffCurve`, `laneOffCurve`, `registryOffCurve`,
`registryProgramdataOffCurve`, `entryOffCurve`, `verifierProgramdataOffCurve`.
Namespace: `AspisR1.JHt_OffCurve`. The `certificates` theorem assembles the exact
`JHs_FixtureCertificates.OffCurveCertificates` expected by
`JHs_InstalledPDA`; use it directly in that module's seven observation theorems.
All seven model off-curve premises are discharged. No premise was added or
changed. No existing proved module or frozen implementation was modified.

Each `...Y` theorem checks the original key through the actual masked,
little-endian `yCoordinate` and field reduction. `JHt_CELLS.json` records the
bytes and numeric y/u/v/inverse/ratio values. All seven u and v are nonzero.
`JHt_Residues` checks v^(p-2) separately from the ratio's Euler power; each
single exponentiation has 256 structural steps with reduced bases. Its
inverse-product and ratio checks use the unreduced numerator/denominator
expressions of OnCurve, so Nat subtraction and reduction match exactly.
The model's sign-bit and noncanonical-Y rules are retained. No canonicality,
subgroup or torsion assumptions were inserted.

`JHt_EulerBridge.no_solution` imports Mathlib's prime-field Euler criterion;
`JHt_OffCurve.fieldPrime` supplies the checked Pratt certificate. The generic
bridge handles zero by contradiction from its explicit inverse and nonresidue
checks, without silently excluding a model case.

JHt_012 was rejected for a linear_combination sign error, fixed in JHt_013.
JHt_015 exposed elaborator unfolding of the concrete OnCurve body; moved the
bridge to symbolic h/y before application. JHt_016 had a wrong State namespace;
corrected to the existing SourceDuplexStep.State in JHt_017. No cap, heartbeat,
recursion-depth or timeout limit was raised. No timeout or memory kill occurred.
All rejected outputs (including their sorryAx diagnostics) are retained and
receive no proof credit.

## Final verification

17/30 Lean attempts used. All seven final modules have accepted matching source
hashes in `JHt_FOCUSED_MANIFEST.json`. `JHt_SOURCE_AUDIT.json` checks every new
theorem has an explicit axioms audit. Accepted final audits are subsets of
propext, Classical.choice and Quot.sound; all concrete residue checks use only
propext. Per-attempt source revision, dirty source hash, imported object hashes,
command, caps, stdout and timing are retained with each receipt. Receipt commands
use one module per `lake env lean -j1 -M7000` invocation inside an admitted
6G/8G systemd scope, MemorySwapMax=0, TasksMax=64. The host cache is retained;
no wallet/key operations occurred. Reservation attempts all admitted; no retries.

The final bridge used the pinned copied cache and compiled dependencies. No
package build, complete frozen manifest, Aeneas/SBF/runtime suite or Kani ran.
No unchanged successful target was replayed. Generator --check and static
source/receipt-manifest validation were run after all final sources were green.
These are focused proof results, not a coherent full formal release replay.
Runtime/dalek/syscall association, deployed artifact pins, decoder/registry
composition, joint non-vacuity, and the deployed security target remain open.
No trust row was adopted and no source-to-runtime refinement is claimed.

## Every Lean check

Exact target is the sole source listed here; exit status is the underlying Lean
command's receipt status (not the transport shell's tail exit). Time includes
timeout/time wrapper overhead. Swap was zero in every check.

| Attempt | Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| JHt_001 | JHt_ModPow.lean | 1 | 1.460076083 | 3307412 | 0 |
| JHt_002 | JHt_ModPow.lean | 0 | 1.507738701 | 3323124 | 0 |
| JHt_003 | JHt_PrattCore.lean | 1 | 0.438061904 | 1025436 | 0 |
| JHt_004 | JHt_PrattCore.lean | 1 | 1.293053034 | 3299560 | 0 |
| JHt_005 | JHt_PrattCore.lean | 1 | 1.290629326 | 3298816 | 0 |
| JHt_006 | JHt_BinaryModPow.lean | 0 | 1.384810758 | 3322868 | 0 |
| JHt_007 | JHt_PrattCore.lean | 1 | 1.424342902 | 3299168 | 0 |
| JHt_008 | JHt_PrattCore.lean | 0 | 1.380195007 | 3317436 | 0 |
| JHt_009 | JHt_Prime.lean | 1 | 3.313951015 | 3331552 | 0 |
| JHt_010 | JHt_Prime.lean | 1 | 3.471301789 | 3339872 | 0 |
| JHt_011 | JHt_Prime.lean | 0 | 5.806709420 | 3384368 | 0 |
| JHt_012 | JHt_EulerBridge.lean | 1 | 1.695466225 | 3311752 | 0 |
| JHt_013 | JHt_EulerBridge.lean | 0 | 1.605585433 | 3324112 | 0 |
| JHt_014 | JHt_Residues.lean | 0 | 1.632671617 | 3320660 | 0 |
| JHt_015 | JHt_OffCurve.lean | 1 | 2.837687768 | 5692032 | 0 |
| JHt_016 | JHt_OffCurve.lean | 1 | 3.273789144 | 5691624 | 0 |
| JHt_017 | JHt_OffCurve.lean | 0 | 3.007980207 | 5724828 | 0 |

Stage commits: e50dd36279 (binary theorem), d9acb54f58 (Pratt certificate);
completed fixture proofs and final receipts are the following stage commit.
