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

## Qualified flat-source follow-up

Committed flat snapshots resolve five additional qualified import names.
The expanded partial traversal now has 4542 repository modules, 142 trusted
direct imports and 39 unresolved names. Of the predecessor 45 selections,
19 are resolved and 26 remain unresolved; another 13 unresolved names are
exposed by the selected source imports. RPz3_source-plan.json records them.
The in-flight serial source phase retains its initial graph; the additional
vertices will be scheduled only after that phase is terminal. No previously
selected source changed in this follow-up.

## Option-only source review

Three further names have identical declarations after removing comments,
whitespace and only maxHeartbeats/maxRecDepth options. Select the existing
committed variant with neither override (no source edit). The final selection
currently has 4545 repository modules, 142 trusted direct imports, 36 unresolved
names. Of the original 45, 22 now resolve and 23 remain unresolved. Remaining
conflicting declaration/import/budget variants stay explicit ambiguities.

## Committed alias recovery

The 45908-file read-only scan found renamed source snapshots. Explicit aliases
and source hashes are in RPz3_aliases.json; RPz3_generic-scan.json retains all
import-signature leads, which are not themselves historical source proofs.
R1FirstFold's canonical FirstFold.lean matches the original retained source
hash 674a9e12...; other aliases have matching named namespaces/import signatures
and require fresh replay. No historical object is substituted. D68 fixes the
PublicPreparation.Funs module of record to the c16 e98bb123... source; that
explicit ruling resolves its conflicting source variants. No candidate edited.

Current partial closure: 4673 repository modules, 143 trusted direct imports,
24 unresolved vertices. Of the original 45 names, 28 are now selected and 17
remain unresolved. Seven further unresolved names are exposed by actual imports.
The exact complete closure size is unavailable until those sources resolve.
All previously scheduled modules remain in the expanded target closure.

D68 also selects the matching PublicPreparation.Types companion. The latest
partial graph has 4674 repository modules, 143 trusted direct imports and 23
unresolved names. Generic filenames Funs/Types/Basic are never matched merely
by basename across unrelated namespaces; those remain missing absent a
specific committed alias. Maximum additional source vertices reachable if
all eligible attempts pass is 576, starting with the 802 validated reused
objects and three unchanged failures. The source-attempt cap is 1450, reserving
50 of the 1500 total attempts for the final batched audits and any necessary
split audits. No use of the entire budget is claimed in advance.
