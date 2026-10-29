# RJQ — actual transcript QueryRange discharge

Target not yet established. QueryRange is discharged; QueryAppend and
FinishContext are open. No complete ledger row or endpoint premise is removed.
No satisfiability witness for all skeleton links is claimed, and the corrected
skeleton remains UNVERIFIED under ruling (v).

## Boundary and exact statement

Worktree: `/Users/dominic/ZK/.worktrees/pv-rjq`.
Branch: `codex/pv-rjq-20261029`; base `c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7`.
Only new `PV_RJQ_` Lean modules were written. All `PV_RunJoin_` sources and
Link definitions are read-only and unchanged. The other live branch/worktree
was not accessed. No Rust, Kani, extraction, ELF, installation or key operation
ran. No push.

`R1Z.PV_RJQ_QueryRange.actual` concludes **exactly**
`PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryRange runs`.
It has no hypotheses other than the existing type/dictionary instances and run
family. Consequently it applies to an actual native run family once supplied,
independently of its model Data and Plan. This is a successful-source theorem,
not a theorem about arbitrary publications satisfying Fields.

Expanding only the unchanged Link, it says that every publication returned by
this run's successful prepare/private-salts/finish chain has
`∀ q ∈ p.queries.val, q.val < 262144`. Neither that range, a successful query
sampler law, Fields, nor any serializer equality is assumed.

The proof uses `x &&& 262143 ≤ 262143`, a list-set invariant, array-update
partial correctness, and induction on scanner fuel. The transcript's named
`queries_factor` equality connects the actual caller to `queries_from_pairs`.
`FinishContext47.source` and isolated Result eliminations then transport the
range through the complete successful finish continuation. Rejected sampler
results, machine failures and divergence are retained; no successful run is
assumed to exist to prove this partial-correctness law.

## Status of each assigned link

- **QueryRange: proved**, exact unchanged Link conclusion, in
  `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RJQ_QueryRange.lean`.
- **QueryAppend: open**, not refuted for an actual run. The relevant corrected
  definition is `PublishContext57.PV_RunJoin_Link_QueryAppend`, with both
  QueryRange and QueryContext. No arbitrary-Fields append claim is made.
- **FinishContext: open**, not refuted for an actual run. A new source trace
  proves the actual sequence through folded leaves, tree/root calls, second
  round encoding, tag 30, final fold, tag 31 queries and the returned publication
  record. The proof also passes tag 32 and the public check. This trace does
  not prove the model Data/Plan associations required by Fields.

## Precise remaining input

At the assigned base, `PV_RunJoin_NativeCallback55.runOf data plans` takes
`data : Phase → OpeningImages54.Data` and `plans : Phase → Plan` as independent
parameters. No actual family fixing these parameters is defined by that
module. Its consumers NativePublication55, NativeAttemptPublication55 and
NativeToRP55 still take them as parameters and assume the publication links.
The reports for rounds 55–57 explicitly retain their producer association.

FinishContext equates actual c0/c1/final bytes to functions of that Data, and
actual semantic/claim/root/inactive bytes to that Plan. Corrected QueryAppend
also requires the Plan's 22 QueryParts to contain precisely the actual opening
bytes. Those conclusions cannot be inferred merely from the names “actual
run” or “runOf”. The missing declaration fixing these families was requested
asynchronously while independent proof work continued. No replacement families
were invented, no successful source bytes were used to define a purported
independent model, and no missing association was promoted to a TrustItem.

`PV_RJQ_FinishTrace.source` exposes all intermediate calls and the returned
publication record for completing that association. It deliberately preserves
`core.option.Option.ok_or` as a dictionary call: in the generic dictionary it
is ExternalFuns.op8, so tree-constructor success alone does not justify silently
replacing it with a native option conversion. The trace makes no such assumption.

Endpoint P removed/added/weakened/changed: **0/0/0/0**. Whole rows removed: none.
The QueryRange link ceases to be an unproved local obligation. The remaining
publication links, eight endpoint fields, three TrustItems, V370/D381/D386,
observer/simulator, coupling, failure independence and side-channel obligations
are retained unchanged. No new top-down skeleton was introduced; no decomposition
or release credit is claimed without a simultaneous-link witness.

## Validation and resources

**17 Lean launches: 10 accepted, 7 rejected; 0 Kani.** IDs 68900–68913
and 68997–68999 were used; 68914–68996 remain unused.
The seven failed sources are retained by verified Git blobs in
`retained-failed-sources.json`. No unchanged failed hash was resubmitted.
68900 failed before elaboration because the new directory lacked `.olean.server`
companions. This was an own-input setup error: read-only companion links were
added, and the invariant source was extended before its next launch. The other
failures were list-membership/substitution elaboration, tuple continuation
exposure, redundant simplification and the invalid generic option-conversion
inference described above. None was a memory/time kill. No limits were raised.

Every launch had allowed:true and admission exit 0 in the **same shell** as
the scope launch; no refusal, cooldown violation, void launch or scope overlap
occurred. All scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, Lean -M7000. Peak RSS was **4488073216 bytes**; swaps 0.

The line-wide failed-source guard is `tools/pv-rjq-20261029/compile.py`, SHA-256
`995e2f448895f70490c11bc8c51327db53400f2cf49e705f1071ea5d5e3eafb6`. It checks failed runjoin and RJQ receipts before
admission, checks ID collisions, and refuses an already submitted ID.

Audit source revision: `cba879e42fe86daaf6a31374e7b3882b7056cb5b`.

| ID | Exact target (R1Z namespace) | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|
| 68997 | PV_RJQ_RangeInvariantAudit | 0 | 1.54 | 4182564864 | 0 |
| 68998 | PV_RJQ_QueryRangeAudit | 0 | 1.66 | 4468965376 | 0 |
| 68999 | PV_RJQ_FinishTraceAudit | 0 | 1.61 | 4448669696 | 0 |

Every new theorem is covered by these audits. Accepted printed axioms are
subsets of propext, Classical.choice and Quot.sound. Original per-module
output/time logs are hash-verified in `original-module-logs.json`. Exact
targets, source revision/hash, import fingerprints, exit, wall, RSS, swap and
axiom output are in `modules-*.json` and `receipt-*.json`.

Reuse under (h6): the private directory has read-only object/companion links
to the runjoin cache and a read-only external-directory link. No imported
source was copied, created, edited or rebuilt. The project-before-external
lookup order is preserved in the relocated private LEAN_PATH; all resolved
objects and dependency fingerprints are compared by SHA-256, and all other
J environment fields match the shared pinned environment. Initial preflight:
3,595 projects, 7,954 direct fingerprints, 5,673 external objects and 5,438 IR
companions, all matching. Final figures are in `fresh-preflight.json`.
The ten historical uncompiled exclusions remain uncredited and unused.
No own scope remains running (`toolchain-and-final-scopes.json`).

No full frozen manifest replay ran: there is no complete publication/skeleton
release result to replay. The audits validate the local discharge and source
trace only. `commits.txt` lists the changes through the audited code revision;
the final evidence-only commit follows it.

Next deliverable: fix or supply the actual Data/Plan producer declarations,
then prove FinishContext and corrected QueryAppend for that family, followed
by the simultaneous-link satisfiability witness and remaining publication
composition. Work on those associations is pending the requested input;
there is no checked actual-run counterexample for either open link.
