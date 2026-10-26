# L187 coherent repository replay handoff

L187 remains open; target not yet established. Branch
`codex/cx-replay-dry2-20261026`. Final receipts and consistency checks are complete.
The only edited files are RPz job evidence under this directory. No push.

## Claim and scope

The owner-approved replay excludes Lean's own Init and pinned Mathlib/Aeneas
libraries. `RPz_trusted-base.json` records exact release-pinned object hashes,
Lean v4.32.0 commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, and the Lake
manifest. Mathlib pin: 81a5d257c8e410db227a6665ed08f64fea08e997.
`RPz_library-provenance.json` qualifies the Aeneas source/object association:
234 backend objects match upstream 220c7ff9cce569dead1e72ef199775b3417493b7
plus the retained Lean 4.32 patch; Fmt and ArraySlice differ and are identified
by their exact selected artifact hashes rather than an invented source pin.

Fresh workspace retained:
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`.
Fresh repository objects are in `RPz_objects`; no old repository objects are
on this job's LEAN_PATH. Toolchain objects take precedence over RPy's retained
Init objects. The actual-source graph selects 4,141 repository modules and
records 108 unresolved source selections. This is a partial graph: unresolved
source may have further imports. Exact graph, source hashes and import order
are in `RPz_source-plan.json`; committed inputs are pinned by `RPz_inputs.json`.

## Unchanged theorem, premises and non-vacuity

`RPz_before-after.md` records the complete identical before/after statement of
`AspisR1.Rc7_Top.deployed`; its source hash is
f471ed2a3eaa6ba76d483fa9201a0f33df5b1cd6d732ef3d4335fd9dd716d38e.
Premises discharged/added/changed: 0/0/0. Ledger-method delta T0/P0/G0/C0.
No quantifier, carrier, failure event, conclusion, trust item, game or metric
changes. Historical conditional non-vacuity is retained unchanged; this partial
replay does not freshly construct or certify a joint inhabitant of all top
premises. No source-refinement premise is relabelled a cryptographic assumption.

## Failures and continuation limits

RPz_001 ImportUnionNamedDiscriminant failed because AeneasMeta library objects
were missing from the initial trusted selection. Subsequent objects use the
explicitly amended trusted-base manifest. This failed module was not rerun.
RPz_247 R1NaturalProjection failed with unsolved goals at lines 28 and 58.
The associated diagnostic sorryAx is a failed elaboration, not an accepted
axiom audit. Dependents of both failures are blocked. No historical object is
substituted to bypass either failure or an unresolved source selection.

Nine unresolved candidate sources were located read-only at immutable revision
d346dc7cb7232f12c4ff930d1e2db320bdc101d9, matching retained source pins in
`RPz_source-recovery.json`. They are provenance leads for the next scoped plan,
not silently substituted into this in-flight replay. No session A worktree or
candidate was edited.

## Receipts and release limits

Every attempt uses the unchanged S2W runner after the unchanged reservation
barrier, one scope at a time: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, Lean -j1 -M7000 -DElab.async=false. Per-attempt JSON records exact
command, source revision/hash, direct dependency object hashes, exit, wall,
peak RSS, swap and cgroup limits; stdout retains #print axioms and diagnostics.
The source-selection plan is stamped a51c005d86 over research input bb0b0f5b12;
new audit modules carry their actual evidence revision and source hashes.
An empty print_axioms list means no explicit query, not standard-only axioms.

No Rust, Kani, SBF, shipped source, key or ELF changes. No ELF rebuild trigger.
Inherited historical ELF pins, not newly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Final result and budget

Budget exhausted: **600/600 Lean attempts, 0/0 Kani**. Attempts RPz_001 through
RPz_600 are contiguous and have unique target module names. RPy's 361 historical
Init compilations remain excluded under the explicit owner scope correction.

- Source replay: 529 attempts, 527 passed, 2 failed; 3,612 selected repository
  modules blocked. Last source module: RPz_529, Hist_Metadata.
- Explicit audit: 71 attempts, 70 passed, 1 failed. RPz_530 failed before any
  query because the counter lacked an explicit Nat type. Its original source
  and diagnostics are retained. Corrected, uniquely named RPz_Audit531 through
  RPz_Audit600 cover all 527 passed source modules with no duplicate declaration
  queries: **19,970 declarations and 19,970 explicit #print axioms results**.
- Overall: 597 passed / 3 failed. Compiler wall sum 1666.0221998049528 s;
  maximum peak RSS 3,873,736 KiB; swap 0. No timeout or memory kill; no increased
  cap; no unchanged compiler rerun. Every source attempt hash matches its
  input manifest. Final process inspection found no live job-specific compiler
  or runner. Reservation and scope receipts are retained per attempt.

`RPz_summary.json` indexes all target/command/source/dependency/resource receipts.
`RPz_state.json` is the source phase only (529 attempts), not the total budget.
`RPz_final-verification.json` records the final coverage/consistency checks.
The post-source-replay object inventory contains 542 fresh object/sidecar files;
all 22,637 trusted-base artifacts were present and hash-identical to their pins.

## Requested axiom findings, with exact scope

(a) `RPz_axiom-audit.json` names **all 527 audited repository modules** and each
module's nonstandard import-closure axiom names, declaration dependency names,
and declaration count. No audited import header is unknown. All 527 import
closures include these 12 nonstandard Init axioms:
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Quot.lcInv`,
`isScalarObj`, `lcAny`, `lcCast`, `lcErased`, `lcProof`, `lcUnreachable`, `lcVoid`,
`sorryAx`. Of these modules, 281 have exactly that set; 239 also import nine
Aeneas axioms; seven also import the seven non-test Aeneas axioms. The exact
per-module lists and axiom owners are in the JSON, with stdout evidence.
This is the complete result for the successfully replayed subset, **not** for
all 4,141 selected source modules or any unresolved extension of the graph.

Every one of the 19,970 audited repository declarations has only a subset of
`propext`, `Classical.choice`, `Quot.sound` as its reported dependencies.
None depends on a nonstandard axiom under Lean's type-and-body traversal.
The presence of an axiom in an import closure is not proof-term use.

(b) Nonstandard axiom reachability from **Rc7_Top.deployed's fresh proof term
remains unknown**: that module was not reached. No historical cached top audit
is substituted for the missing coherent replay.

(c) **The set of FunsExternal axioms reached by Rc7_Top.deployed, and its Rust
external mapping, remains unknown**, not verified empty. No such dependency
occurs in the audited repository declarations, but the blocked top cannot
inherit that partial conclusion.

## Next concrete deliverable

Do not launch another Lean attempt under this exhausted allocation. The next
scoped plan must resolve the 108 source selections, including the nine
hash-matched immutable candidate recoveries; explicitly reconcile the amended
library selection for ImportUnionNamedDiscriminant; and isolate the two
R1NaturalProjection unsolved goals. Extend the committed-source graph and
continue the dependency-order replay using these retained objects. Do not
silently import historical repository objects or change theorem statements to
skip blockers. Then compile Rc7_Top, query its actual fresh proof term, complete
the remaining module audits and map every reached generated external to Rust.
Only that can close the outstanding coherent-replay and top-reachability rows.
No premise-removal, fresh joint non-vacuity, source-to-ELF reproduction or
100-bit release conclusion is claimed by this partial run.
