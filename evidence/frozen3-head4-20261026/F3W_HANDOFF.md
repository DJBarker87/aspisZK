# Frozen3 fourth-round handoff

S2 OPEN; deployed 100-bit target not established. Branch
codex/cx-frozen3-head4-20261026. SINGLE DELIVERABLE NOT CLAIMED CLOSED.
No F3W_Join.raw_join_or_collision was installed under a weaker statement.

## Checked obstruction and stopping condition

The unguarded rejected-run full-eval version of the requested universal
statement is false. F3W_Obstruction.no_unconditional_raw_join proves this on
the actual installed source, canonical byte Input, complete frozen3 verifier,
and exact charged complete-account event of the bound (Q=0). Oversized public
bytes reject before any source oracle read; frozen3's sampler always reads.
The bound gives a collision-free H, so the collision disjunct cannot rescue
full eval equality. The account source/project/select may vary with each
submission; the result is not based on an unrelated fixed account trace.
See F3W_OBSTRUCTION.md for exact quantifiers and source references.

This DOES NOT refute F3U_CollisionJoin.Join, which has source acceptance as an
explicit guard. A clarification was requested because "accepted installed
source" suggests that inherited guarded interface, while the requested
rejected-branch method suggests the stronger unguarded statement. No answer
arrived before stopping. If the guarded interface is intended, the remaining
charged-account association is still OPEN. No new domain restriction, source
acceptance premise on the unguarded statement, model gating or trust item was
silently added. The explicit checked-obstruction stop rule was followed;
unused compile budget was not consumed on a refuted rejected-run extension.

## Before/after statements and actual progress

BEFORE F3V_AllWorldAcceptance.accepted:

    forall s H, retained preparation/query owners -> sourceAccepts s H ->
      exists e i p q data t, same source-derived witnesses/facts AND
      (prefixCollision OR exists actual primitives x,
        retainedFinishLeaves x -> prefixCollision OR modelAccepts i H).

F3V_ByteLog separately decomposed the complete source log but did not join it
to the complete model's ordered log on those same universal witnesses.

AFTER F3W_Canonical.accepted:

    forall s H, retained preparation/query owners -> sourceAccepts s H ->
      exists e i p q data t, same source-derived witnesses/facts AND
      (prefixCollision OR exists actual primitives x,
        retainedFinishLeaves x -> prefixCollision OR
          eval H (source c hashv (input c s)) =
          eval H (F3_Model.verifier D (input c s))).

This is a checked stronger continuation, not the deliverable. Source acceptance
constructs the SAME TX1 Run, saved Vec and TX2 calls. F3W_SourceLog.evaluated,
FirstLog.log and SecondLog.log factor all ordered source reads; LogJoin.joined
composes sampler/preparation, batch0, checkpoint write/resume and batch1 logs;
Aligned.values carries the SAME Input/Parsed/queries/data/actual finish
witnesses; SourceHead.head and F3U_CanonicalNative.joined transport to the
original submission's canonical Input. Duplicate reads are preserved.

Discharged locally: the former universal complete source/model log-equality
and canonical-Input transport gaps, under the retained owner/finish leaves and
original prefix collision. Retained: the five F3T_Leaves families on actual
primitives, preparation/query/geometry/arithmetic owners, and all actual-top
history/runtime/source/ELF/other-cone obligations. Added: no cryptographic or
runtime trust item. No independent accepted native pair, THIS-H fixed-native-SHA
realization, assumed model acceptance/preparation success/log equality is used.

The pure two-call source consumes its own saved.deref. Its empty-history
CheckpointVersionBinding is constructed explicitly; this does not discharge
physical cross-transaction persistence. Prefix collision is NOT renamed as
charged complete-account collision. F3U_AccountEndpoint/F3U_ConditionalBound's
SAME experiment association remains to be proved for the guarded target.

## Ledger and non-vacuity

Actual top BEFORE and AFTER: Rc2_Top.deployed, unchanged source SHA256
24460608f3b6099aff4581cf34a8a3339c565a934365cf96cf480eec6e39b4fd.
019 prints its complete kernel statement and axioms. It is byte-identical to
starting revision9e5d7bfe7fa064a91decffd438a79cb3134e1c11.

Ledger method: Rc2_premises.json/Rc2_LEDGER.md atomic conjunctive leaves and
quantified law families, SAME witnesses/guards, deployment-alias deduplication;
no structure/binder-count subtraction. No new deployed theorem exists.
Actual82T/171P ->82T/171P; deduplicated actual+deployment88T/184P ->88T/184P.
Delta ZERO. Neither local log equality nor an obstruction deletes a top premise.

No headline or accepted joint fixture/non-vacuity construction was attempted,
as instructed. Source-success implications do not establish acceptance exists.
The malformed-input/collision-free-H existence in the obstruction is not an
accepted fixture and is not credited as non-vacuity of retained release laws.

## Validation, provenance and resources

19/100 actual single-module Lean attempts;15 pass,4 development failures;
0/0 Kani. No dependency build or package replay. 003 underconstrained digest
arguments/missing import,009 wrong saved-size source/dependent rewriting,
014/015 sampler API/elaboration errors were corrected. Failed recovery
sorryAx prints are retained and excluded. No timeout, memory kill, cap increase,
unchanged rerun, parallel own scope, reservation bypass or launcher repair.

All15 current F3W modules (including Audit) match a successful source snapshot.
F3W_Audit prints all18 new top theorem axioms: only propext,Classical.choice,
Quot.sound. It also prints the exact guarded Join and actual Rc2 baseline.
Final019: target F3W_Audit.lean,exit0,wall6.246020600s,peakRSS5373424KiB,swap0,
source revisionf16b42a643 (dirty source; full revision/hash in receipt).
Maximum attempt RSS5380876KiB; every swap count0.

Command: lake env lean -j1 -M7000 -DElab.async=false -o F3W_Audit.olean F3W_Audit.lean.
Each compiler ran in ONE own admitted systemd scope with MemoryHigh6G,
MemoryMax8G,MemorySwapMax0,TasksMax64. Unchanged existing S2W runners and coherent
SInt2 host cache reused. Per-run receipts record exact command, source revision/
SHA, dependency/sidecar fingerprints, status,wall,RSS,swap,cgroup and axiom lines.
F3W_attempts.jsonl,F3W_source-manifest.json,F3W_theorems.json,F3W_FINAL.json
index those receipts. git diff --check passes; source scans find no forbidden
proof shortcuts or resource overrides. This is focused cached composition,
not a coherent frozen-release rebuild.

Only new F3W_ modules and assigned evidence changed. No shipped source or
cfg(kani) harness, session A worktree/candidate, other prefix, wallet/key/account
or authority operation. ELF rebuild trigger did not fire. Inherited pins,
NOT freshly reproduced:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Stage commits:1e17445ae1,c51afe0bae,bff09f1bb4,f16b42a643; final audit/handoff
commit follows. No push. Next owner decision is the exact guard/rejected-log
relation; the acceptance-guarded route then needs SAME charged-account
association, not another assumed join wrapper.
