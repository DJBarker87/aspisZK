# Lane A session6 handoff — PARTIAL; requested completion not achieved

Branch `codex/pv-lib-20261107`, continued from
`9e72b8360546e8e59c25101961856fad85d5c0e9`. No push/merge. Lane B files,
package modules, frozen specs, row consumers, implementation and ledger are
unchanged. Inherited handoff: session6/INHERITED_HANDOFF_SESSION5.md.
The accepted D989 v2 inventory is retained byte-for-byte; no reinventory.

## Import surface and what is established

`import PV_LIB_A_StoreActionTable` exports the named definition
`PV_LIB_StoreActionTable.v2`. It consolidates the22 supplied source-store
projections and their named documented meanings. **This is a PARTIAL table,
not the completed source-faithful table requested by the lead.** All111
accepted inventory candidates, including89 unsupplied meanings, are retained
in session6/STORE_ACTIONS.json. Missing entries never mean no-write.

`import PV_LIB_A_StoreActionMachine` exports
`PV_LIB_StoreActionTable.step`, directly extending the OWNER-aware
`PV_THR2_OwnInitInterpreterBridged.step`. One symbolic `agreement` and
`advance_agreement` retain the exact resource channel, registration, operator
and bridged allocation actions away from supplied table entries. Inline
bodies are not intercepted a second time. `native` exposes the entire partial
model graph, including its undefined arm. This is not full source adequacy.

`PV_LIB_A_ActionAnswers` proves whole-delivery equality for spurious weak
CAS failure, plus both CAS variants' pending and fault branches. Strong/weak
Result::Err performs no source write. The named Arc clone projection retains
the increment before overflow abort; scope increment retains its overflow
restoration branch. No success, no-write, non-spurious or overflow-free
restriction was added to a row interface. Native value/order/backing bindings
are still lower proof obligations, not new endpoint premises or T fields.

## Checked gaps preventing D984 credit

`PV_LIB_A_ActionAdequacyGap` and `PV_LIB_A_ReplyAdequacyGap` establish:

- Every504 generic selects bool-only504. Aggregate replacements are rejected,
  although their same valid transparent source replacement prefix is defined.
- On that unsupported arm, pending and panic become undefined. The pinned
  reply rule instead keeps pending running and maps client panic to abort.
  World/events preservation alone therefore does NOT retain every answer.
- Count1 rejects both nonlast Arc/Weak meanings. Last-strong payload Drop,
  implicit Weak guard, dangling/last Weak and deallocation remain missing.
- Installed wrappers214/168/122/128/454/4/14 have no table entry. Nested atomic
  tokens do not supply their complete native source-store effects.

session6/CELL504_SPECIALIZATIONS.json retains the six raw504 calls and exact
expanded T/destructor metadata: bool417; tuple437/629; Option477;
SpawnHooks602; generic762. See session6/MODEL_FINDINGS.md for theorem names,
actual raw sites and limits. These are checked local model counterexamples,
not original-entry reachability or violations by the frozen Rust.

## Remaining work in the requested order

1. Complete the table with every v2 writer's exact named meaning;89 candidate
   meanings remain unsupplied. Do not promote this partial import to complete.
2. Implement typed old-T Drop AFTER504's source replacement; complete486/584/683
   last-reference/guard/deallocation semantics and opaque wrapper effects,
   retaining every answer. An arbitrary Store transformer or success/nonlast
   premise does not discharge this obligation.
3. Then corrected-machine Range93, f6 and OwnInit histories. This session
   did not claim any such history or repeat their original-interpreter runs.
   All detailed session5 history/numbering/resource/registry obligations remain.

The work stops at the checked source/model adequacy gaps, not ID or compute
exhaustion. The requested complete table and histories are unfinished.
Endpoint premises removed0/added0; new T fields0; slot status changes0.
PLIB_MAP and REMAINING record the partial import and exact gaps. All170
statuses remain118 qualified INSTANTIATED,35 MISSING,12 WAITING,5 SPEC-ERROR.

## Verification and IDs

Five new proof/support modules and one driver compile accepted; eight focused
attempts47416–47423, with two repaired syntax/elaboration failures47416/47421.
Exact failed sources are compressed with hashes. COMPILES.json, SUPPORT.json
and individual receipts record target, source revision/index blob, exit,
wall, peak RSS, swap and summary-based #print axioms.

ONE strict raw audit47491 of29 new roots passed: exit0,5.48s,
peak6584260KiB,swap0, source revision
`4c81e511a532f37b12d838158c0ae64f2d1f3bf3`. Only
propext/Classical.choice/Quot.sound; unresolved0; summary mismatches0.
Raw driver/walker unchanged except module/root arrays; graph archive, manifest
and hash retained in session6. No repeated raw/full manifest/runtime gate.
Every attempt used standalone STREAMB_SLOTS=3 admission and a single scope
with6G/8G/swap0/Tasks64/-M7000. No launcher range or shared host changes.
Next focused47424–47489; raw47492–47499. Inherited463xx was already spent and
was not reused. No live task scope. VALIDATION.json checks exact scope,
source/receipt hashes, unchanged accepted inventory and unchanged slot records.
Target not yet established.

Session7 in progress from03c3c72b143:47424 passed CellSetBegin, deriving the
replacement and retaining old T plus the exact emitted destructor metadata.
This is not yet a complete arbitrary-T destructor/table repair. No caller
history is promoted. Session7 receipts preserve the6G/8G/swap0/Tasks64 caps.
47425 passed all six exact raw504 metadata checks. Only417/437/629 have
trivial drops;477/602/762 explicitly do not. Generator --check passes.
47427 passed CellSetPatch after retaining/fixing47426's two local reduction
errors. It adds exact metadata-selected bool/tuple504 delivery on the OWNER
machine, with a full-reply theorem and agreement against the OWNER base. The
arbitrary-T, last-reference and wrapper gaps are not marked closed.
47428 passed ActionPolling: an explicit applied phase prevents supported native
source prefixes from being executed again on each pending poll. retry and
pending_retry preserve the exact request/config/world/event suffix. This is a
partial source model, with the same unimplemented typed Drop/wrapper coverage;
it is not promoted as the completed v2 or as an OwnInit history.
47430 passed the exact source-backed Thread214 field/count projection after
retaining47429's match-reduction failure. This is source-backed only; native
world/result and OWNER-only backing are not silently called closed.
47431 passed the exact Option<ThreadId83> interpretation: pinned ThreadId is
Copy, so its Option destructor has no callback/store effect. This adds477 to
the recognized effect-free set without classifying SpawnHooks602 or generic762
as trivial. Source archive/hash is session7/STD_THREADID.json.
47433 passed WeakDropSource after two repaired elaboration issues at47432.
The source prefix now distinguishes dangling/nonlast/last, and deallocation is
a retained completion stage rather than a prefix incorrectly run on pending.
This is source-only lifetime support, not complete allocator/OWNER adequacy.
47434 passed StoreActionTable7, an explicitly PARTIAL extension preserving
PV_LIB_StoreActionTable.v2 unchanged/importable. v2Source/sourceStep combine the
new copy504/source-backed214/staged683 projections and retained pending phases.
source_agreement uses the same OWNER base and resources. No full table or
caller-history credit is claimed.
47435 passed source count1/deallocation/root-frame lemmas. Polling review found
that the simple ActionPolling/Table7 retry is NOT correct for reply-dependent
CAS or Vec push/append: their pending projection is identity and completion
must still apply the deferred operation. Those intermediate retry graphs earn
no full-machine adequacy credit. A fixed deferred overlay follows; old models
and all their results are retained unchanged.
