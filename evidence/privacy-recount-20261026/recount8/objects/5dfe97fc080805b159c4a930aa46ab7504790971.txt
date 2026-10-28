# Runjoin45 — selected coefficient dictionary and ordered Vec assembly

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `a9044ce8cd26aeee6cbc1f80d5ade7684c52b882`,
resume LOG D411. Source revision at final validation
`7c4a3d6de275f204551a26654abdf08a147a62be`. Assigned IDs **61200–61299**, audit IDs **61297–61299**.

**Target not yet established. Whole ledger rows removed: 0.**

## Checked coefficient source result

`PV_RunJoin_CoefficientsCaller45.complete` proves the actual complete current
`prover.opening_coefficients` Result on all 29 original 1024-entry wide columns,
with the exact ordered permuted vector and length 29. Inputs are arbitrary wide
cells; constructor success or desired coefficient values are not hypotheses.
The existing `CoefficientArray44` theorem supplies the exact row permutation.

The op255 dictionary structure was inspected before the replacement proof.
Fourteen small named projection modules preserve that single field through each
installation layer. `CoefficientInstalled45` composes their equations and the
retained source association. The large predecessor dictionaries are locally
irreducible; no complete dictionary equality is normalized. Lean 4.32 requires
`allowUnsafeReducibility` for locally overriding definitions explicitly marked
reducible; this affects elaboration hints only, not kernel checking or a
resource limit. No recursion, heartbeat, memory or other limit was raised.

`CoefficientsThread45` identifies one symbolic source-loop step with a finite
fold, retaining failures/divergence. `CoefficientsCell45` separately proves one
actual read, coefficient call and Vec push; its Copy dictionary is explicitly
built from the selected operations. `CoefficientsVector45` aggregates by
induction on the remaining column count. The 29 columns are never unfolded
simultaneously. No individual cell needed a concrete recurrence reduction.

Rejected run-44 sources and their uncompiled dependent draft remain uncredited.
Run-45 rejected candidates are retained by Git blob and hash. The isolated cell
exposed that an implicitly inferred base-dictionary Copy was different from the
actual selected-dictionary Copy. This was corrected explicitly; the generic
coefficient law already covers arbitrary Copy dictionaries. Failed attribute,
layout, instance and proof-composition candidates are not counterexamples.

## Stored weight state and retained gap

The next source calls are op252 (constructor), op253 (raw row) and op251
(materialization), sharing the exact object stored in ExternalTypes.op25.
`WEIGHT-NEXT.md` names the next model consumer and the required state association
with `ProverCommitWeightsStorage53.State`, `weights53.new`/`row`, and
`ProverCommitWeightsMaterialBinding53.run`, before use of
`ProverCommitOpeningModel53.exact_result`.

The existing batch-2 source closure resolves without a cohort gap under the
recorded EJR/freeze/h5 precedence. It requires 86 project modules absent from
the private cache. `weight-source-resolution.json`, `weight-source-staging.json`
and `weight-focused-preflight.json` record hashes and topological dependencies.
The other job's cached objects were not loaded: its LEAN_PATH prefix differs
from the required coherent cache (`weight-object-reuse-decision.json`).
Exactly **64** of those prerequisites compiled once in topological order.
**22 remain uncompiled**, beginning with `PV_B2_F_MutationModel`; their exact
order is in `pending-weight-prerequisites.json`. This prerequisite validation
does not prove the weight/opening association. No unchanged accepted module
was rebuilt.

**Step (2) remains incomplete.** Both actual opening constructors, their stored
weight/materialization and claim evaluations, all intervening transcript and
Result branches, folded domains and trees still require the complete caller
association. The 22-query append, six node multiproofs/publication indices and
`publish_compact`'s complete ordered proof bytes remain open. Steps (3) and (4)
are not started, respecting the requested order. Both complete native ROMView
decoders, installed native helper effects, the security-model proof-byte
equation and RustRealRefinement remain open. OracleBridge38 retains its single
named op227 callback hypothesis, unchanged and unused for credited endpoint
removal. Op227 is not the sole remaining refinement gap.

## Boundaries and admission

Endpoint premises removed/added/weakened/changed: **0/0/0/0**. V038, V045, V163,
V165, V167 and V244 remain. No new whole-row credit is claimed for V262/op255
or V258–V260/op251–op253; local source association and private prerequisite
validation retain their narrower scopes. All eight PV_RunJoin_Premises fields are unchanged:
source_V045, E1_V329, native_fill_V336, native_ledger_V337, byte_blind_V338,
kernels_V339, disclosed_V038 and observerOracle_V038. TrustItems remains exactly
entropy_law, entropy_kernel and observation.

Observer/simulator, coupling, bad/query events, failure/divergence observations,
public guards, failure independence and side-channel obligations are unchanged.
Native compiler cohort/features/profile/ABI, D188, allocation/TLS/filesystem,
Drop/unwind and K-1/K-2 qualifications keep their previous scope. No new native,
Kani or deployed-artifact credit is claimed. No shipped source, key/account,
root checkout, other worktree, shared source/cache or protected soundness file
was changed. No push, merge, extraction, ELF rebuild, native differential or
unchanged full regression was run. The frozen Rust/client diff from 82566acdfb
remains empty; historical artifact evidence keeps only that unchanged scope.

Before the first compile, the own wrapper was changed for ruling (t): admission
runs in the **same shell command** as the scope, with `&&` requiring exit 0 and
a second explicit check of allowed:true. Full refusal cooldown is checked before
submission. All **100** launches satisfy that chain in `admission-launch-audit.json`: zero
refusals, zero cooldown violations, zero void launches. No shared launcher or host infrastructure was edited.

## Validation

Initial read-only preflight: 2764 project pairs, 5802 direct fingerprints, 5673
external objects and 5438 IR companions; all match. Every compiler runs one
module in one scope with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64 and Lean -M7000. Exact targets, source revisions/blobs/hashes,
dependency fingerprints, commands, exit, wall time, RSS, swap and original
axiom output are recorded per attempt. The **100-attempt Lean budget is exhausted**, IDs 61200–61299, with **86
accepted / 14 rejected**, **0 Kani**. Accepted modules comprise 19 new source
proofs, 64 pinned prerequisites and three focused audits. All printed accepted
axiom sets are subsets of propext, Classical.choice and Quot.sound. The 14
rejected sources are hash-verified retained Git blobs. No memory kill, timeout
or unchanged failed-source rerun occurred.

| ID | Focused audit target | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 61297 | R1Z.PV_RunJoin_CoefficientAudit45 | 0 | 1.88 | 4405800960 | 0 |
| 61298 | R1Z.PV_RunJoin_WeightPrerequisiteAudit45 | 0 | 1.78 | 3951669248 | 0 |
| 61299 | R1Z.PV_RunJoin_SourceAudit45 | 0 | 2.20 | 4447981568 | 0 |

Peak scope RSS was **4447981568 bytes**, with zero swaps throughout. Scope
intervals are disjoint. `original-module-logs.json.xz` hash-verifies all 100
original output/time pairs. `receipt-*.json` and `modules-*.json` retain exact
source and dependency fingerprints, metrics and printed axioms. These are
focused checks, not a complete frozen-manifest or endpoint release replay.

Final read-only preflight verifies **2850 project pairs, 6008 direct import
fingerprints, 5673 external objects and 5438 IR companions**, all matching.
Initial and final full preflights are compressed with uncompressed SHA-256
sidecars. The private runjoin32-lean workspace remains pinned and reusable;
Lean is 4.32.0 at commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35. The final
inventory confirms zero own running scopes. One premature read-only inventory
correctly detected the then-running 61297 audit; it was deferred until all
audits completed, without any compiler rerun or infrastructure edit. This
own scheduling correction is recorded in `local-input-corrections.json`.

Stopped on the **100-attempt budget**, not on a checked counterexample. The
next concrete deliverable is to compile the 22 remaining pinned weight
prerequisites, beginning at `PV_B2_F_MutationModel`, then prove the association
of the exact installed stored object and its raw/materialization Results with
the retained weight model. Compose that with the completed coefficient caller
and both actual opening constructors into `ProverCommitOpeningModel53.exact_result`,
retaining all transcript/Result branches, before the query/node append,
publication indices and complete ordered proof-byte equation.

`commits.txt` records commits since entry; a final evidence-only freeze commit
follows its generation. No privacy target or whole ledger row is claimed
established.
