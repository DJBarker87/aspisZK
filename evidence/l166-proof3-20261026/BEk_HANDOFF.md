# L166 proof3 handoff — 26 October 2026

**PARTIAL; L166 OPEN; target not yet established.** Branch
`codex/cx-l166-proof3-20261026`. No push or merge. Only BEk_ modules and this
receipt packet changed. No shipped/cfg(kani) source, session A worktree or
candidate, wallet/key/funds/authority, wire format, feature or parameter changed.

## Exact status of the four requested stages

1. `BEk_ReachedInputs.cuts` and `BEk_OriginalInputs.selected` derive both
   concrete native-SOURCE batch argument tuples from the fixed accepted native
   wrapper pair, and attach ARU's original queried-address cylinder/replay.
   **The physical internal batch observation, borrow/allocation geometry and
   attempted recorder have NOT been extracted.** Wrapper Entry/heap/allocator
   states are retained as the same fixed inputs; they are not asserted equal
   to an unobserved internal cut.
2. `BEk_LocalAssociation.of_step_projection` proves BothSlots for the explicitly
   source-operational interpreters under a primitive returned-value/common-state
   step projection. It uses the same proof/Prepared/roots/folded-root/ordinal;
   both AcceptedPath and RejectedPrefix follow, with no rejected-state/error-kind
   equality. Port4B scratch induction is imported unchanged. **This is not the
   requested physical instance.** See BEk_OBSTRUCTION60.md and the checked
   original-cylinder recorder-independence theorem.
3. `BEk_OriginalJoin.accepted` consumes ARU_OriginalFactory.original,
   OriginalLaw, Join and Charges on the original partial account, original
   adversary, same H/project/select/event and same budgets. It preserves
   original wrapper outcomes and SOURCE-COMPUTED attempted cost and derives
   source/model ordered equality, model acceptance and physical-VIEW recovery
   OR the SAME charged original-account collision event, with Q+2965 audited
   reads. No fresh interpreter/law or global NativeAt at H is introduced.
   `BEk_QueryPrefix.transport`, `BEk_CutExport.queried`,
   `BEk_Returning.agrees`, `BEk_SlotExport.current/stage` feed the SdkC/ARU
   computed Returning logs into the exact BEj Prefix consumer without global
   P1 at H. Their physical local-law premise is explicit and remains OPEN.
   The complete physical local-to-global composition is therefore not claimed.
4. **BEk_Top.deployed with L166 removed is NOT delivered.** No alias or assumed
   local law is presented as premise removal. The actual top remains Rc10.

## Before/after and recount

The exact actual root is `AspisR1.Rc10_Top.deployed`. BEk_BEFORE/AFTER_SOURCE
retain its complete identical source. Fresh before/after unelided kernel
prints and their equality/hash are recorded in the final validation packet.
No quantifier, carrier, failure event, conclusion, constant or binder changes.
L166 is a deployment-only obligation, not an existing root binder.

BEk_recount.json independently tallies BEk_ledger_rows.json from the pinned
Rc10 atomic-family inventory, deduplicating shared witnesses/guards/installed
slots and the L185=L159 alias. Native-local/global finish families stay separate.
Actual antecedents: **83T/12P/13G/0C**. Deployment-inclusive:
**89T/16P/13G/0C**. Before=after; **delta0T/0P/0G/0C**.
No added/reclassified/removed row. Helpers and statement audits earn zero
row-removal credit. L166 remains OPEN. ARU's pointwise original-cylinder
consumers are available and used, but its own universal representation-range
and unrestricted-Runtime root obstructions are not silently discharged.

## Non-vacuity and next deliverable

`BEk_Nonvacuity.rejected` has two identical successful attempted addresses,
a pure source rejection, and a native-decoration rejection with a different
error kind and mutable final state. It satisfies precisely the weak local law.
`step` supplies a satisfiable primitive projection with a changing private
Boolean and a live common counter. These are positive-query local models,
not real-byte native batch fixtures. The inherited Rc10/ARU non-vacuity
statements are audited with their full remaining native/game/owner/fixture
premises; no joint realization is claimed.

`BEk_RecorderIndependence.original` keeps ARU original support/replay and
DERIVED reached current batch inputs while showing that Result/final-carrier
facts do not determine an independently decorated recorder. This is an
interface non-implication, not a shipped native execution/bug/attack.

Next: extract and relate the instrumented physical native batch, its actual
recorder and common live carrier on the same reached allocation/borrow geometry;
then instantiate the checked step projection and consume BEk's queried-address
slot exports and ARU original-cylinder join. No wait for ARR/ARQ_Join.Target.
D188 Parse-versus-panic remains a fidelity note; rejected error kinds are
irrelevant under the ruling. No new trust item or owner ruling is proposed.


## Final validation and resource receipts

**Budget exhausted:100/100 Lean invocations;94 pass,6 excluded development
failures;0/20 Kani;0 dependency rebuilds.** The first20 invocations checked the
new proof modules and actual-root environment;21..97 are77 DISTINCT inherited
statement/trust-boundary inventories, not new proofs or release progress.
98 is non-vacuity-scope audit;99 is the fresh combined partial-proof audit;
100 is the final unchanged actual-root audit. No further proof invocation.

Final partial target **BEk_FinalAudit.lean (099)**: exit0,
wall2.467533308023121s,peakRSS5541980KiB,swap0;
revision anchorcbe93c1d0dd40f707564a0e8f715ca6b4bcbc4f5 plus dirty source SHA256
9e0ca2f6c8254f3425568897f26f3fa04aa758b10e05f7965eb8bafaec7edd98.
It imports all13 new proof modules and prints all17 new public theorem axioms.
Only propext/Classical.choice/Quot.sound occur (or none). Full statements and
axiom lines are in stdout/receipt; failed compiler sorryAx outputs are excluded.

Final root target **BEk_AfterRoot.lean (100)**: exit0,
wall2.4170999220223166s,peakRSS5509400KiB,swap0;
revision anchorcbe93c1d0dd40f707564a0e8f715ca6b4bcbc4f5 plus dirty source SHA256
282a63a034c4ccf01ab23d801fcacb5b7052455d2749243f7a7379232af524c9.
Before004/after100 kernel prints are byte-identical and unelided,113647bytes;
SHA25639b9c00e7c4251663a83dfaf148365ef53e03d6c9702623e10e008f64ed1be2e.
BEk_root_cache.json pins the reused root object. This is fresh focused cached
validation, NOT a root rebuild or coherent frozen-release manifest replay.
The literal source/statement and all actual binders remain unchanged.

Total compiler wall227.3742265549954s;maximum peakRSS5565636KiB;
swap0. Every invocation used lake env lean-j1-M7000-DElab.async=false,
one admitted scope at a time,MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.
Every receipt records exact target/argv,revision,source SHA256,selected dependency
objects/tool fingerprint,exit,wall,RSS,swap,limits and full axioms/errors.
Reservation stdout/stderr was captured BEFORE uploads. All100 own scopes are
terminal. No timeout,memory kill,cap increase,unchanged resource-failure rerun,
package replay,launcher repair,foreign job kill or barrier bypass occurred.

Failures001/002 were missing transitive-object/path-order diagnostics;
006/008/009/018 were corrected elaboration errors. The recorded path-order
change puts the existing ARU r4 cache ahead of the partial package directory;
no inherited source/object was rewritten or rebuilt. Existing SInt2 workspace
and pinned caches were reused. BEk_HOST_FINAL.json verifies18 current own host
source hashes,records source/object hashes+sizes and all terminal scopes.
Five unused audit object files were removed. The13 accepted proof modules'
objects remain in the coherent shared cache for lead reuse; no second corpus,
Rust target,solver temporary files or disposable build workspace was created.
No binaries/objects/ELFs/archives are committed.

BEk_validate.py PASS:100-invocation budget,caps,source snapshot hashes,
standard axioms/all new public audits,byte-identical root,independent atomic
recount and source-only scope. BEk_VALIDATION.json and BEk_attempts.jsonl retain
metrics and full per-invocation metadata. Raw compiler/wrapper logs are kept
verbatim, including pretty-printer whitespace. Source/script/document whitespace
checks are separate from those raw logs. The attempt60 gate file is finalized.

No shipped/cfg(kani) source changed,so the ELF rebuild trigger did not fire.
No Rust,Kani or SBF build ran. Inherited pins,NOT newly rebuilt/reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Stage commits before final receipt commit:95b5c124b5 baseline;
65c29c0a1a reached source inputs;252caedefe conditional step/prefix;
ad71c92d20 original-cylinder composition;cbe93c1d0d attempt60 obstruction.
All commits stay local;no push or merge. The100-bit release target remains
not established. No complete physical BEk_Top is claimed.
