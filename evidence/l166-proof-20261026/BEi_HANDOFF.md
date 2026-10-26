# L166 proof handoff — 26 October 2026

**PARTIAL; L166 OPEN; target not yet established.** Branch
`codex/cx-l166-proof-20261026`. No push, merge, shipped-file change,
other-prefix module change, session A worktree/candidate edit, key or wallet
operation. Host proof launches stopped under local-lean rule5, not on proof
budget exhaustion. The requested `BEi_NativeBatchCut.observation` and
`BEi_Top.deployed` with L166 removed are **not delivered**.

## Checked claim and exact limits

`BEi_Execution.Executes` is a small-step relation for the existing source Code
language with a stateful digest primitive. `sound`, `complete`, `unique` and
`iff_run` prove its exact deterministic interpretation. A failed/diverging
syscall retains its changed state AND its attempted recorder occurrence;
`BEi_ExecutionBind` preserves the SAME intermediate carrier/history through
continuations. These are source semantics, not a physical runtime admission.

`BEi_RecorderCut.exact_cut/source_cut` exports the chronological recorder delta
as `after.drop before.length` and proves it equals the computed source log
when actual operational step evidence and digest value binding are supplied.
`BEi_BatchPrefix.export_cut` gives its complete attempted-address ideal prefix
and a source-count bound on all outcomes. Duplicates and a final failed call
remain occurrences. This interface is usable by ARQ **once the physical cut
has been associated**; no freely selected successful native log is introduced.

`BEi_BatchCut.current/stage` specializes this to the installed current/stage
batch Result and exact `SdkC_BatchSource.currentCode/stageCode` inputs.
`BEi_AcceptedCut.construct` constructs source operational execution from source
acceptance. `BEi_SourcePair.same_pair` uses `SdkC_BatchPair.same_pair`'s SAME
f/s SourceCuts and actual Prepared/root arguments. Both local executions are
constructed; the intervening state/history are explicit. It does not delete
checkpoint/other calls between batches or identify those arguments with an
independently selected model witness.

`BEi_PhysicalGap.extension` shows at EVERY fixed outcome that a longer
recorder decoration can preserve the full returned Result and final carrier
while violating BEh's Law. `retained_facts` preserves unrelated propositions
without recorder arguments. `operational_excludes_extension` shows that an
actual operational association would exclude that decoration. These are
interface non-implications, **not counterexamples to shipped native code**.

## What remains to prove

The adopted D188 extraction boundary still returns values, without a physical
native state/log interpreter. The current SDK/runtime admissions do not by
themselves construct `Executes` for a physically observed batch cut. The
checked P6 owned scratch induction and source log/accounting results are not
reopened or credited twice; none is silently promoted to this missing instance.

First deliverable after the launcher is restored: define/extract the concrete
reached native batch observation and prove its local state/log step association
on the SAME proof bytes, Prepared arrays, roots, ordinal and borrow geometry.
Use existing runtime/library admissions and the accepted Port4B scratch
composition. Then prove the exact `BEh_Scope.BothSlots` instance, not a
premise whose fields contain that desired instance. The two unchecked
`BEi_NativeBatch*.PROPOSED.lean.txt` drafts are source-interface explorations,
not candidate closure evidence; they live outside lean/.

Dependency order remains: actual local native observation -> BEh logs and
accepted carrier projection -> existing SdkC source logs -> existing
RPx_Transport.transport and RPx_AccountCharge.charged -> ARQ same-experiment
join -> actual deployed root. No conditional top composition was checked
before the infrastructure stop. The local physical association remains
separate from ARQ, so this packet cannot claim closure modulo ONLY ARQ.

The global join is exactly the other job's `ARQ_Join.Target c hashv copy
allocator id D a Q0 Q1`: for every H, accepted ORIGINAL account output implies
literal installed-source/model evaluation equality OR the charged collision
event on `Hiq_RecordedJoint.program` of that SAME original account, using
`ARQ_Observer.project` and `ARQ_Observer.select c id`. Adversary/projections/
installation/budget are fixed before H. Full read-only statement/projection
snapshots and hashes are in `BEi_reference_ARQ_*.lean.txt` and
`BEi_ARQ_reference_pins.json`. They are unmerged reference interfaces, not new
imports, proofs, trust or removal credit.

## Before/after and ledger delta

The actual root is `AspisR1.Rc10_Top.deployed`. Its full source and unelided
inherited kernel statement are retained in `BEi_BEFORE_*` / `BEi_AFTER_*`.
The sources/statements are byte-identical; no quantifier, hypothesis, carrier,
failure event, collision branch, conclusion or constant changed.
`BEi_recount.json` reuses the unchanged root's Rc10 atomic-family inventory,
including shared-witness/guard/installation deduplication, separate native and
global finish families, and the L185=L159 alias. It is not a fresh root replay.

Actual antecedents: **83T/12P/13G/0C -> 83T/12P/13G/0C**.
Actual plus non-alias deployment: **89T/16P/13G/0C -> 89T/16P/13G/0C**.
Removed0, added0, reclassified0. L166 remains deployment-only; L159/L181 remain.
The local operational relation and digest-binding hypotheses are visible in
local lemmas only; they are not added to or counted as removed from the root.
No new trust item, owner decision, source adoption or security metric change.

## Non-vacuity

`BEi_ExecutionComplete.complete` constructively inhabits operational execution
for every source code, starting state/history and partial digest handler,
including its failure/divergence alternatives. `BEi_AcceptedCut.construct`
and `BEi_SourcePair.same_pair` construct successful local source executions
from the existing accepted-source premise on the SAME witnesses. No False
premise or assumed BEh Law is used to manufacture those constructions.
Inherited `BEg_Nonvacuity.success/rejection/failed_read` supplies positive-query
state-changing examples; it was not replayed. The unchanged actual-root
`Rc10_Nonvacuity.composed` remains conditional on the native/game/owner/snapshot
hypotheses. Its source hash and successful historical receipt are pinned in
`BEi_reused_evidence.json`. No joint real-byte release fixture or proof of
physical native prefix inhabitation is claimed.

## Validation and mandatory infrastructure stop

**17/100 Lean compile attempts, 13 passed, four corrected elaboration failures;
0/20 Kani.** Twelve final new modules match successful source snapshots; all
24 successful printed axiom audits use only propext/Classical.choice/Quot.sound.
Failed004/006/011/015 are retained and excluded from accepted evidence; incomplete
failed elaborations' printed sorryAx is not an accepted theorem. Revision017
supersedes014's standalone consecutive-batch interpretation by retaining the
intervening state/history explicitly.

All compile targets/commands, exact source revisions/hashes, selected object
fingerprints, exit statuses, wall time, peak RSS, swaps and full axioms/errors
are in per-attempt receipt/source/stdout/time files and `BEi_attempts.jsonl`.
Compiler wall total41.2480407449184s; maximum peakRSS5292608KiB; swap0.
Every launched scope terminated. Reused coherent SInt2 objects and unchanged
S2W launchers; one scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/
TasksMax64, Lean-j1-M7000-async=false. No dependency build, package replay,
full frozen-manifest replay, Rust, Kani or SBF build. Attempt006's transient
vanished cgroup scan was retried after30s and succeeded; both diagnostics are
retained.

Reservation-only018: target `BEi_NativeBatchCut.lean`; no source upload,
compile, scope, RSS/swap measurement or axioms result. The required reservation
command failed twice, with the missing-receipt diagnostic retry after30s:

```
python3: can't open file '/home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py': [Errno 2] No such file or directory
```

`BEi_018-stop.json` and the pre-scp barrier log record exit2 and the stop.
Local-lean rule5 explicitly says: "Do NOT build or repair build/launcher/
monitoring infrastructure. If the launcher or host misbehaves, stop and report
the exact error in one paragraph; the lead fixes infrastructure." The launcher
path was not changed, no alternate barrier was selected and no infrastructure
was repaired. The unused budget is83 Lean/20 Kani; the stop is mandatory
infrastructure policy, not exhaustion or an Aeneas/Kani/proof timeout.

`BEi_validate.py` performs only static packet validation. Exact unchanged-root
historical checks and their standard axioms are explicitly marked reused in
`BEi_reused_evidence.json`; this is not a coherent frozen-release rebuild.
No shipped/cfg(kani) file changed, so the ELF rebuild trigger did not fire.
Inherited ELF pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Stage commits:465b907da1 baseline;d6ef541a67 operational cuts;
837a5caa4f concrete source-cut projections/physical-gap evidence; final handoff
commit follows. All local, no push.
