# Inversion zero-boundary handoff — 2026-10-27

**Target not yet established. V380-inversion remains OPEN. No endpoint premise
was removed.** Stopped at exhaustion: 100 Lean attempts and 10 Kani runs.
No checked protocol-level witness-pair counterexample was established.

Branch: `codex/pv-inv-20261027`. Base/source inspection pin:
`9c4bfcc830c09f8d85fd1ed7996f8d9dcf059c84` (research). Worktree:
`/Users/dominic/ZK/.worktrees/pv-cb3`. Host directory:
`/home/dombarker/project-offloads/codex-pv-inv-20261027/`.
Stage commits and validation history: [HISTORY.txt](HISTORY.txt).
No push/merge. No crates/programs changes, ELF rebuild, key creation or cleanup.

## Inventory and per-site status

[INVENTORY.md](INVENTORY.md) contains source file:line anchors, caller edges,
operand provenance, exclusions and corrections. [candidates.json](candidates.json)
retains 341 lexical candidate source lines with source hashes, including tests,
declarations and non-field inverse functions. This is an auditable source review,
not a compiler-proved complete call graph. The adopted CT binary/source association
is not inferred from the research source or historical receipts.

| Reachable family | Provenance | Proved result and residual status |
|---|---|---|
| statement/logup.rs:200,213, copy helper | chi minus witness-derived compressed tuple; lambda/chi challenges | PROVED conditional source arithmetic: `NativeRegistry.producer` derives the slot through the actual extracted arithmetic compression reference, using raw tuple/tag input correspondence, registry membership, active row and NoPole. `RawNative.packed_nonzero` and `NativePackScan.guarded_packing` prove every reached packed slot has canonical nonzero subtraction, false whole-value zero test and canonical successful inverse. Whole native site remains OPEN: concrete registry/bank/tag/active-row association and the headline coupling/event join are not supplied. |
| probe/host_sumcheck.rs:30 | public i,j<28; interpolated values are witness-bearing but do not enter denominator | PROVED extracted initializer: `InterpolationSource.source_inverse_operand` supplies nonzero den and successful inverse for every bounded i, without an inverse-success premise. Native source/caller association to the owned extraction remains an existing proof obligation. No probabilistic charge needed for the mathematical denominator. |
| core/field.rs:1004,1011,1019,390–398,213 | inherited from callers | PROVED `NativeQ`, `NativeNormQ`, `NativeNormC`: canonical nonzero input produces successful QM31 inverse; actual CM31 and M31 norm operands are nonzero. This is conditional on each caller's input and source association, not blanket caller closure. |
| core/circle.rs:40, including transcript fallback | challenge t; denominator 1+t² | PROVED algebraic singular-root characterization, exclusion outside a subfield containing ±i, rational-image properties. Native zero/fallback can occur on challenge inputs. Complete raw-challenge joint law and native fallback association remain OPEN; no probability is assigned to an unrelated charge. |
| z4/z9c.rs:42,121,304; z9b.rs:51,59,71–73,108; z9.rs:298–320 | challenge-derived certificate pivots; public constants/domain indices | PROVED local pivot-selection and nonzero-selection facts; Kani checks source control slices, not elimination arithmetic. Global certificate/geometry native association and challenge-to-observer joint law remain OPEN. |
| z4/z9c.rs:336 and probe.rs:2292 via chain_targets/normalize_d | challenge alpha[9]-1/2 | Can be zero and rejects. The caller supplies challenges, not witness columns; this alone does not prove joint simulation. OPEN; no unproved bad-event inclusion or changed bound. |
| statement/pool_v1/pair_tree_profile.rs:221, when including the pre-prover constructor | witness/coin-derived occupied sentinel | PROVED guarded source-reference inversion after explicit zero rejection (`Sentinel`). Full native constructor/retry/joint-law association OPEN. |
| statement/pool_v1/pair_forest_copy_builder.rs:159,182 | witness-derived change commitment sentinel | Total exponentiation, no operand-zero branch; included as an alias, not silently omitted. Variable-latency remainder observation remains existing L2/L3 work. |

Generic R0 quotient/chord/phi and WideExact inverse definitions are present in
the scan but no call from this S2 prover/certificate source path was established.
The encoder calls division-free phi_inverse. Compile-time basis inversions are
public. Historical alternate-protocol/rank/test inversions are excluded with the
reasons in INVENTORY.md. Source-review completeness remains an audit limitation.

## What advanced

`RegistrySlot` uses the existing producer/consumer slot-Nodup theorems to prove
that each model row-slot sum equals its single registry endpoint value.
`NativeCompress`, `TupleModel`, `WordTuple`, and `CompressTuple` connect the
source arithmetic compression reference to that tagged tuple formula.
`NativeRegistry.producer` retains explicit INPUT correspondence, rather than
assuming the desired compressed operand equality as in the predecessor.
The native registry enumeration and trace-bank correspondence are still required.

`GlobalSlots`, `GlobalSafety`, `GlobalOrigin`, `GlobalProjection`, and
`GlobalPairs` cover interleaved keyed producer/consumer updates, including
zero-weight overwrites and failed slot allocation. `GlobalNative`/`GlobalScan`
prove false whole-value zero-test lists for reached slots after successful
packing, without assuming endpoints were pre-grouped by row/side. These are
structural references with extracted arithmetic, not an extracted whole native
builder or a complete native L2 observation interpreter.

`PoleMass.zeroEvent` existentially includes all model packed rows/weights/sites;
`contained`, `mass`, and `PoleUnion.eight_attempts` bound the entire zero event
by the original NoPole failure allowance, without another union per call.
The charged summand is **`8 * (4096 / ((2^31-1)^4-1))` inside
PrivacyR1Final.modelError**, already retained in the headline. It is not the
freshBudget, seed budget(2^64), fuel charge or 16/2^486 summand. No native event
is declared contained merely by naming that charge. SAME-headline coupling
association remains unproved, so this is not a discharged deployed charge.

`ZeroTraceLimit` checks a tiny source-expression counterexample to the inference
“nonzero verdict implies equal short-circuit limb-test trace.” It is not a
valid-spend witness-pair attack or a statement about adopted CT machine code.
False whole-value tests do not close all branch/address/operand observations.
The observer remains complete; no such effects are dismissed.

## Validation and receipts

[INDEX.md](INDEX.md), [SUMMARY.json](SUMMARY.json), [AUDIT-MANIFEST.json](AUDIT-MANIFEST.json),
[AXIOMS.md](AXIOMS.md), and each J*/K*/receipt.json retain targets, exit, wall,
peak RSS, swap, source revision/hash, direct-import object hashes, command/caps
and printed axioms (Kani: N/A). Snapshots and raw diagnostics survive failures.

- J42100–J42199: 100 charged attempts, 79 successful. Every final source hash
  has a successful receipt: 76 source modules plus three audit modules.
  J42197–42199 were reserved and used only for the final audit. No ID reused;
  no reservation refusal, cap increase, local Lean compile or concurrent scope.
- J42199 `R1Z/PV_Inv_Audit3`: exit 0, wall 0:01.49, peak RSS 4,109,124 KiB,
  swap 0, revision `31864a2613`. Maximum across all runs: 4,115,336 KiB.
  The 145 final printed declarations use only propext, Classical.choice,
  Quot.sound, or no axioms. Failed elaboration's sorryAx output is not evidence.
- K01–K10: 10 runs, 9 passing structural checks and 1 CLI rejection. K02 fixes
  K01 by adding the required terse output option. No timeout, chained-field
  SAT gate, inverse stub, or whole shipped-function equivalence claim.
- Shared launcher: -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0;
  actual launcher/own Kani scope TasksMax=64. All GNU-time Lean swaps are zero.
  Kani uses taskset CPUs0–3, -j4, 180-second cap. Admission diagnostics were
  retained before copying sources. Host restoration flag and rulings (a)–(k)
  were read. No shared existing source/launcher was rewritten.
- Missing interpolation dependencies were derived into eight NEW private-name
  PV_Inv modules. [derived-interpolation.json](derived-interpolation.json) pins
  originals/transforms. No existing module-name/source association was replaced.
- Conversion timeouts J42178–42180 were replaced by the generic `TupleModel`
  and named `WordTuple` split; J42181–42183 passed at unchanged caps/options.
  No unchanged failed input was retried with higher resources.

This is one final focused union/import/axioms audit, not a coherent frozen
release replay. No unchanged full regression or artifact suite was run.

## Ledger and next deliverable

Before/after: **V380-inversion OPEN → OPEN**, all nineteen predecessor L2
whole rows retained. Removed endpoint/deployment premises: none. Added or
changed endpoint premises/trust items: none. `simE`, bound, observer, release
pins and the three-field T cap are unchanged.

Next: extract or structurally bind the concrete native registry enumerator,
raw trace-bank tuple reads, tags, static slot assignment and active-mask
membership to the existing copyLinks/model trace. Instantiate the global packing
and compression theorems for both deployed LogUp sites on the original headline
RunJoin, then prove containment in its actual retained bad-event union and the
full observed zero-test trace law. Independently bind the certificate/circle
challenge records and remaining domain facts. No protocol counterexample is
claimed in place of these missing proofs.
