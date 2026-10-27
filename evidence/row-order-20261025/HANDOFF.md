# RowOrder handoff — 25 October 2026

Branch codex/cx-row-order-20261025. **S2 OPEN; target not yet established.**

## Established

1. `AspisR1.RowOrder_AcceptedPairHistory.accepted_pair_history`
   (`lean/RowOrder_AcceptedPairHistory.lean`) exports the SAME accepted D189
   pair, exact expanded/owned trace and schedule, account observations,
   selected semantic Claims and conditional Required14 as SInt2. It additionally
   constructs the checkpoint history indexed by the actual saved Vec and
   actual TX2 checkpoint, preserving the runtime key, ledger and events.
   It derives checkpoint/proof/public byte identity and checkpoint size1768.
   SourceCuts is an output, not an added premise. Its local consumer is
   `RowOrder_History.on_d189_cuts` in the research Lean directory.
2. `AspisR1.RowOrder_FrozenSchedule.decision` (same research directory)
   gives the exact frozen2 model-order normal form, including both batches'
   rejected prefixes and the six ordered repeated checkpoint reads. It uses
   the actual resumed completeState in finish. This is a model theorem, not
   a source/model refinement.

## Retained premises and uncompleted headline

The complete checked accepted-pair statement is printed in RowOrder-007/stdout.log.
Its premises remain SDK borrow trust; std copy; allocator/runtime entry
admissions; the installed candidate's native/digest extraction, P1 and syscall
ports; the two actual accepted wrappers; expanded child port and marks; the
named writer/reader, first-entry/multiproof/S8 child joins; runtime
CheckpointVersionBinding on the actual post1 payload; and P2Prime. The candidate
Ops, semantic boundaries and Claims std installation are unchanged from SInt2.
The runtime history protection condition itself has not been discharged.
No trust item, cryptographic assumption, event, carrier or metric was added or
changed. Reindexing a protected history is not a proof of Solana protection.

**Not completed:** per-row source-to-frozen2 assembly, the raw canonical
AcceptedRunJoin, or a deployed per-attempt soundness theorem. In particular,
the known source dictionary joins are reflexively inhabited for arbitrary
model dictionaries; they cannot identify one with frozen2. The Q1/Q2 source
installations still need compatible same-return preparation and reader state,
actual reached-call ports and the indexed authentication/ordered effects in
the port table. Shape/scan/finish are the other workers' rows, not assumed
closed here. No whole-driver equality premise was introduced to hide these
obligations, and no new per-row structure is presented as discharging them.

There is also a checked-endpoint prerequisite gap: Port1_CanonicalHeadline
exports the older Claims/bound, whereas OraclePortHeadlineFrozen2PerAttempt
requires the unrestricted join. A canonical version needs a new proof using
canonical runtime_transport with Frozen2StartChargeProbability.failure_bound.
The read-only dependency preflight found201 absent project modules for the
canonical headline/per-attempt/model-order closure in the supplied workspace
(see dependency-preflight.json). Building that entire missing closure exceeds
the100-attempt budget; no such build was launched and no alternative cache or
build infrastructure was introduced. This is not budget exhaustion and is
not evidence that a theorem is false. The concrete next deliverable is a pinned
compatible row dictionary and its raw canonical order proof, plus a coherent
compiled headline closure before endpoint application. P7 remains the named
compiler trust boundary per C3-BIN13:35; no extra Lean lowering obligation is
claimed.

## Validation and frozen target

Eight Lean attempts, zero Kani/Rust runs. All use the coherent SInt2 workspace,
the unchanged existing launchers, -j1 -M7000 -DElab.async=false and individual
6G high/8G max/swap0/tasks64 scopes. No timeout, memory kill or cap increase.
001–003 are excluded elaboration failures;004–008 pass. Attempt007 strengthens
006 with key/ledger/event preservation. No unchanged source replay.

Final focused composition/axioms audit: `RowOrder_Audit.lean`, RowOrder-008,
exit0,1.708035344s,peak5212880KiB,swap0,source b7c0386d57 with dirty new audit
source; its exact SHA is in the receipt. All new top declarations print no
axioms or only propext/Classical.choice/Quot.sound. Every attempt records target,
command, revision/source SHA, direct dependency fingerprints, cgroup, exit,
wall,RSS,swap and full axiom output. validation-summary.json indexes them.
This is a focused coherent import check, not a full frozen-release manifest
replay or fresh rebuild of historical imported objects. The SInt2 object/source
and final closure manifests remain the provenance for reused dependencies.
`git diff --check` and the new-source forbidden-proof-construct scan pass.

No shipped or cfg(kani) file, other worker module/worktree, key, parameter,
feature, wire format or release artifact changed. ELF rebuild trigger did not
fire. Inherited pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Final budget8/100 Lean,0/60 Kani. All stage commits are local; no push.
The deployed soundness and100-bit release target remain unestablished.
