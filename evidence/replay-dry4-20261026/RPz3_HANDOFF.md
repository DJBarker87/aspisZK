# L187 committed-source coherent replay continuation

S2/L187 OPEN; target not yet established. Final validation is complete for the
ready partial frontier; the full top dependency closure is blocked. Branch
`codex/cx-replay-dry4-20261026`; no push. Only RPz3 evidence and query modules
under this job's evidence directory are changed.

## Scope and source selection

The graph is parsed from committed source starting at `lean/Rc7_Top.lean`.
It currently selects 4674 repository modules, 143 trusted-library direct
imports and 23 unresolved names. This is a partial lower bound, not the exact
complete closure: unresolved sources may add imports. No out-of-closure source
module is scheduled. The original 45 source selections resolve to 28 committed
sources, 14 missing CompPoly sources and three genuine conflicts. Recovered
imports expose six additional unresolved names. Exact mappings, hashes and
candidate variants are in RPz3_source-plan.json, RPz3_aliases.json and
RPz3_source-selection.md. No live session A worktree/candidate was edited.

The 828 predecessor fresh objects are retained in
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`. Of these, 802
are valid for the selected unchanged source/dependency chains. Their object
hashes and 2386 direct dependency edges (778 actual host paths) were checked:
no mismatch or conflicting dependency pin. The other inherited selections are
invalidated or out of scope, not silently substituted into a green context.
Only pinned Init/Mathlib/Aeneas and the explicitly recorded library base are
reused as trusted libraries; CompPoly is not silently added to that exception.

## Four inherited failures

Complete original receipts/resources/errors are in RPz3_inherited-failures.json.
ImportUnionNamedDiscriminant failed on missing AeneasMeta; R1NaturalProjection
has unsolved goals at lines 28 and 58; SemanticCallExtraction.Types could not
write its nested output path. These selected sources are unchanged and are not
retried under the binding source-change rule. NaturalProjection's alternate
success file changes definitions and statements, so is not a repair of the
selected failed source. The prototype discriminant adapter has incompatible
attribute syntax and is not substituted for the canonical adapter.

R443BoundedRejectionMass's committed canonical source adds the missing
Mathlib.Tactic.FieldSimp import. That changed source passed as RPz3_007:
exit 0, wall 1.23 s, peak RSS 1829560 KiB, swap 0. All three printed theorem
axiom sets are [propext, Classical.choice, Quot.sound]. This is an import-gate
repair, not a removed soundness premise.

## Unchanged theorem, ledger and non-vacuity

RPz3_before-after.md retains the complete identical statement of
AspisR1.Rc7_Top.deployed, source SHA256
f471ed2a3eaa6ba76d483fa9201a0f33df5b1cd6d732ef3d4335fd9dd716d38e.
Premises removed/added/changed: 0/0/0; ledger delta T0/P0/G0/C0. No quantifier,
carrier, failure event, conclusion, security metric, trust item or game change.
No fresh joint inhabitant of all top premises is constructed. Historical
conditional non-vacuity is retained without strengthening. No source-refinement
gap is recast as a cryptographic assumption. The unchanged statement text does
not certify semantic identity with every historical object cohort. Source
selections are explicit replay inputs, not a new source-adoption or
source-to-ELF equivalence result.

## Completed formatter and axiom audit

Fourteen successful batches (100 modules each, final batch 78) cover all 1378
green module contexts: 60248 structured declaration queries and 60248 full raw
#print axioms results. There are 60210 distinct global names, 31 repeated names
(38 extra context occurrences), and no repeated owner/name query. No identity
of proof terms across repeated names is inferred. All audited import headers
match the committed-source graph, with no missing module or completion error.

The all-declaration standard-only gate is FALSE: exactly 72 formatter-family
records use the inherited 37 nonstandard axioms. No audited declaration outside
those two families uses them. The direct reference audit found two generated
sharing edges: each parser's CoreCmpPartialEqError.eq uses its
CoreFmtDebug.fmt.match_1. Both matchers have no axioms; both equality functions
use [propext, Classical.choice, Quot.sound]. RPz3_FORMATTERS.md gives full names
and query references. A whole-prefix deletion would remove shared matchers.

Separate lead-approved cleanup candidates are the Debug fmt and Debug record
definitions in each parser, with their generated native proof helpers.
Preserve or regenerate the pure shared matchers and rebuild their consumers.
No generated file was changed. Fresh Rc7_Top proof-term reachability and its
FunsExternal-to-Rust mapping remain UNKNOWN; no historical top audit substitutes
for the missing fresh top.

## Artifacts and validation limits

All attempts use the unchanged S2W command runner, one capped scope at a time,
MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64, Lean -j1 -M7000.
Exact target, command, source/dependency hashes, revision, exit, wall, RSS,
swap, scope and raw axioms/errors are retained per attempt. Compiler wall
excludes SSH/admission waits. The host quiet-window shim held RPz3_073 outside
any scope until 17:55 UTC; it was neither bypassed nor edited.

No shipped source, Rust, Kani, SBF, wallet key or ELF changed; no ELF rebuild
trigger. Historical pins only, not newly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Final budget, exact claim and next deliverable

**591/1500 Lean attempts; 0/0 Kani.** Source: 577 attempts, 576 passed, one
raw serializer failure retained. RPz3_543 exposed a pair/triple iterator ABI
mismatch. The existing committed adapted Funs source paired with the selected
P6 model passed at 571; six dependent modules then passed. RPz3_ADAPTER.md
records this changed-source retry. No unchanged-input retry, timeout, memory
kill or cap increase. All 14 audits passed. Overall: 590 passed / one failed.
Compiler wall sum 2093.088474536722 s; peak RSS 4625476 KiB;
swap 0. Exact per-target resources, revision, source/dependency hashes, commands
and printed axioms/errors remain in the attempt receipts.

Final frontier: **1378 green contexts** (802 reused + 576 newly passing), three
unchanged failed vertices, 3293 blocked selected modules and 23 unresolved names.
There is no ready unattempted source. Unused budget is not called exhausted:
further source attempts require resolved sources or changed failed inputs.
No attempt is spent on out-of-closure or unchanged failed modules.

RPz3_final-verification.json reports no consistency error: all 591 attempt
numbers contiguous; 5771 direct dependency edges over 1515 actual host paths
hash-match; all selected source hashes match; all reused objects are unchanged;
no live job compiler/runner. All 22637 pinned artifacts are present. The sole
inherited drift is S2H_reservation.py (f5b8318a... to 195657d7...), already
recorded by RPz2; no Lean/library or used runner drift. The default Lake
repository object directory is absent. Raw launcher line-wrap whitespace is
preserved; source/metadata whitespace checks are recorded separately.

Next: resolve the 14 missing CompPoly sources, three original source conflicts
and six newly exposed names; repair/authorize changed-source treatment of the
three inherited failed vertices. Retain the shared pure formatter matchers in
any approved cleanup. Continue only the actual committed import closure using
these objects, then compile Rc7_Top, print its fresh axioms and map every
reached generated external to Rust. Full closure, joint non-vacuity and
source-to-ELF correspondence remain open. Premises removed: zero. The 100-bit
release target is not established.
