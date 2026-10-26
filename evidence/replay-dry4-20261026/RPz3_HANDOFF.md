# L187 committed-source coherent replay continuation

S2/L187 OPEN; target not yet established. This is an in-progress packet until
final verification and the final budget section are filled. Branch
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
gap is recast as a cryptographic assumption.

## Formatter audit

The two original generated parser formatter families and their 37 nonstandard
axioms are listed in RPz3_formatter-static.json. In the initially scanned
committed sources, only their own definitions and local formatter registrations
refer to them. This source scan is not a fresh top proof-term certificate.
Their proposed removal is a separate lead-approved step; no generated source
was removed or changed. Final batched constant-reference audit: pending.

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

## Final budget and next deliverable

Pending serial source frontier, batched audits and final consistency checks.
No release, complete-closure, top-reachability or 100-bit security claim.
