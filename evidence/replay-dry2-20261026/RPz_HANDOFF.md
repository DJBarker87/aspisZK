# L187 coherent repository replay handoff

L187 remains open; target not yet established. Branch
`codex/cx-replay-dry2-20261026`. This handoff is finalized after the receipts.
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
