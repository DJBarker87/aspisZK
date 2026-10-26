# Committed import closure

Revision acf38be800b73709426019baf85a3db32a40196b, root lean/Rc7_Top.lean.
The traversal selects 4507 repository modules, 136 trusted-library direct
imports and 41 unresolved vertices. This is a partial transitive closure;
imports beyond missing/ambiguous sources are unknown. The predecessor graph
is not treated as the target list: one prior selected module is out of scope.
Fourteen of its 45 unresolved names now select committed research content;
31 remain unresolved and ten newly exposed names are unresolved. All candidate
paths and hashes are recorded in RPz3_source-plan.json. Canonical committed
research sources take precedence; conflicting non-diagnostic variants remain
explicit ambiguities rather than invented selections. No live worktree read.

Four inherited failed vertices remain in scope. ImportUnionNamedDiscriminant
(missing AeneasMeta), R1NaturalProjection (unsolved goals at lines 28 and 58),
and AspisR1SemanticCallExtraction.Types (missing nested output directory)
have unchanged sources and will not be retried. R443BoundedRejectionMass's
committed canonical research source adds Mathlib.Tactic.FieldSimp, unlike the
failed retained host snapshot; only this changed source is eligible for retry.
The original full errors are in the predecessor receipts, to be indexed in
this job's final report.

Authorized budget is the job-specific 1500 Lean / 0 Kani. Reuse unchanged
fresh objects with recursively unchanged inputs; compile only ready vertices
of this graph. Audit at the end in groups of at most 100 modules. One capped
scope at a time, -M7000, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.
The host clock was already 17:35 UTC: no special parallel-window privilege
is relied on; the reservation barrier governs admission.

Before/after theorem identical; ledger delta T0/P0/G0/C0. No new joint
non-vacuity witness or premise removal is claimed. Target not yet established.
No shipped source or artifact change; inherited ELF pins remain historical.
