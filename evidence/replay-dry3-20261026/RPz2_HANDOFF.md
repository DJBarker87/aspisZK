# L187 continuation handoff

L187 and S2 remain OPEN; target not yet established. Branch
`codex/cx-replay-dry3-20261026`. No push. Only this job's evidence was changed.

## Exact claim and source frontier

The continuation attempted 303 source modules once each: 301 passed, two failed.
Together with the unchanged 527 predecessor objects, 828 repository modules
have fresh objects in `/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz_objects`.
No historical repository object was substituted. The actual-source graph has
4361 selected repository modules, of which four failed and 3529 are blocked;
45 unresolved source selections may extend the graph further. No unattempted
module is ready. The remaining partial-graph critical-path lower bound is 304.
Exact graph, paths to failures and source receipts are in RPz2_source-plan.json,
RPz2_frontier.json and RPz2_001 through RPz2_303. Last source target:
RPz2_303 ExtractedPrefixHeaderBytes. Source hashes all match the selection plan.

The initial plan recovered nine immutable hash-matched session A sources and
70 unambiguous dependencies. A further 141 source selections came from retained
host source/object associations. Their exact text is preserved. Directory
association with a matching historical object is explicitly qualified; an
independently retained original source receipt is not invented. Conflicting
variants remain unresolved. RPz2_receipt-provenance.json gives the exact commit
and path of each replay snapshot, including raw receipts that used the label
`retained-host-source-snapshot`. No live session A worktree or candidate was edited.

## Failures retained, not retried

Inherited RPz_001 ImportUnionNamedDiscriminant and RPz_247 R1NaturalProjection
have unchanged selected sources and were not retried. A different retained
NaturalProjection source was located but has different definitions/statements;
it was not selected or compiled.

RPz2_016 AspisR1SemanticCallExtraction.Types failed to write its object because
the nested output directory was absent. Directories were then prepared only for
unattempted modules; this failed compiler invocation was not repeated.
RPz2_213 AspisV8R19.R443BoundedRejectionMass has unknown `field_simp` at line 87
and an unsolved `value_mass` field identity at line 80. Its diagnostic sorryAx
is failed elaboration, excluded from accepted axiom evidence. Dependents of all
four failures are blocked. The failures were not hidden or bypassed.

## Unchanged theorem, recount and non-vacuity

RPz2_before-after.md preserves the complete identical before/after statement of
AspisR1.Rc7_Top.deployed. Its source hash is
f471ed2a3eaa6ba76d483fa9201a0f33df5b1cd6d732ef3d4335fd9dd716d38e.
Premises removed/added/changed: 0/0/0. Ledger delta T0/P0/G0/C0.
Actual antecedent remains 83T/26P/13G/0C; deduplicated with deployment rows
89T/31P/13G/0C. No quantifier, carrier, failure event, conclusion, game, trust
item or metric changes. Historical conditional non-vacuity is retained, not
freshly certified: this replay constructs no joint inhabitant of all top premises.
No source-refinement gap is renamed a cryptographic assumption.

## Artifact and toolchain pins

The 843-file object inventory retains all inherited fresh files unchanged.
All 22637 pinned artifacts are present. The sole inherited-pin difference is
the shared reservation script: old f5b8318a7cdb5e03e5221a2e3c43c274fc0fe499afc53f2b6a091e2d4bd27180
(1473 bytes), observed 195657d75fd2a290c236f078fca4247929f214d4f693532ae1fb4d5edc34d893
(2451 bytes). No Lean/library object or S2W command runner drift was found.
This job did not edit the shared script. Per-attempt cgroup limits are separately
verified in receipts. RPz2_pin-drift.json records the distinction.

No shipped source, Rust, Kani, SBF, wallet key or ELF changed; no ELF rebuild
trigger. Historical hashes, not newly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Audit and final budget

Budget exhausted: **600/600 Lean attempts, 0/0 Kani**. Source replay
303 attempts (301 passed, two failed); explicit audit 297 attempts, all compiled.
Overall 598 passed / two failed. Exact per-target command, exit, source/hash,
direct dependency hashes, wall, RSS, swap, scope and full axiom/error output
are retained. Compiler wall sum 1291.497885842109 seconds; maximum peak RSS
4688908 KiB; swap zero. Every scope verified MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, with Lean -j1 -M7000. No timeout, memory kill,
cap increase or unchanged compiler retry. No further Lean attempt is authorized.

All 301 new successful module contexts were audited: 9512 structured query
records and 9512 full raw #print axioms results. There are 9459 distinct global
names: 42 names recur under different reported owners/import contexts, giving
53 extra name occurrences. No owner/name pair is queried twice. The earlier
plan for globally disjoint declaration queries was not achieved; the actual
module groups are disjoint, while generated ownership varies by context. No
claim that these repeated names identify identical proof terms is made.
RPz2_audit-findings.json retains all context records and repeated-name lists.

**Standard-axiom gate FAILS for two modules.** 299 audited modules have only
standard dependencies. AspisR1RecordParser.Funs and
AspisR1PrefixAggregateParser.Funs each have 36 query records using nonstandard
axioms, 72 total. Their Debug formatter definitions and generated helper/axiom
constants reach 37 distinct nonstandard axioms: 18 native-decide axioms per
parser, plus Aeneas.Std.core.fmt.Formatter. The complete names/dependencies are
in RPz2_audit-findings.json and RPz2_axiom-audit.json, with raw proof-query
output in RPz2_565 and RPz2_583. These generated sources are unchanged retained
sources; this job did not write these axioms. They are not accepted as standard
axioms, and no formatter-to-top reachability conclusion is inferred.

RPz2_396 has 140 complete raw print results, but the existing runner's regex
stores 139 and truncates 16 names containing apostrophes. The omitted result
and malformed parsed lines are preserved in the findings JSON; the runner and
original receipts were not altered. The structured collectAxioms records and
full stdout cover all 140 queries. This discrepancy is reported, not hidden.
The actual fresh Rc7_Top proof term was not reached. Its nonstandard axiom
reachability and FunsExternal-to-Rust mapping remain UNKNOWN, not verified empty.
A successful subset audit cannot replace the missing top replay.

## Next concrete deliverable

Resolve the formatter nonstandard-axiom gate and query-context identity issue,
then the 45 source selections and four failed vertices under a new scoped
plan; preserve all 828 valid fresh objects and avoid unchanged failed replays.
Reconcile source/toolchain provenance before repairing the field_simp import or
selecting any alternate failed source. Then continue the actual import graph,
compile Rc7_Top from fresh repository objects, query its actual proof term and
map every reached generated external to Rust. Complete remaining closure replay
and artifact correspondence before any L187 closure or security release claim.

## Final consistency checks

RPz2_final-verification.json confirms contiguous RPz2_001–600, 600 unique
compile targets, complete audit coverage of the 301 new passing module contexts,
9512 raw print results, no repeated owner/name query, no source/receipt hash
mismatch, exact caps and zero swap. It explicitly marks the standard-axiom gate
FAILED and globally unique names FALSE. RPz2_manifest-validation.json verifies
all 4361 selected source hashes; all 220 recovery snapshots match. Final host
inspection found no live job compiler/runner and no default Lake repository
object directory. The shared admission script still has the observed hash.
Staged diff whitespace checks pass; staged paths all have this job's prefix and
contain no binary artifacts. No release, full-closure or top-axiom claim is made.
