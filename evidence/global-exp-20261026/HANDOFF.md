# GExp handoff — budget exhausted; requested premise removal incomplete

Branch `codex/cx-global-exp-20261026`, worktree `cx-global-exp`.
**Target not yet established. L157, L159 and full L088 remain OPEN.**
No checked shipped-source counterexample. No push. No shipped/cfg(kani) changes.
Stop reason:100 charged Lean attempts, including3 prelaunches;97 actual Lean
invocations (6 missing unchanged dependencies included),0/20 Kani. No further
proof/build invocation is authorized under this task's exhausted budget.

## Exact established claim and before/after

`lean/GExp_FinalAccepted.lean`, theorem
`AspisR1.GExp_FinalAccepted.accepted_pair_unified`, passes in094 and is audited
in100. Its hypothesis binders are byte-identical to
`SdkD_Accepted.accepted_pair_unified`; see `GExp_before-after.json`.
It preserves EVERY predecessor conclusion on the SAME f,s,outer,pre,middle,
fs,ss,cuts/history witnesses and derives both complete source logs, composed
TX1/TX2 source acceptance and an all-world22585 query envelope for the
fixed-pair source program. No chosen log, second existential cut, extra native
success or compatibility hypothesis is introduced.

`GExp_InstalledPrepare.associated` derives COMPLETE concrete preparation
Associated from existing extraction.digestSource, without total syscall
success. `GExp_PrepareTrace.source_log` identifies the full typed preparation
observations with SDK-lowered native reads on all outcomes. Complete TX1/TX2
source erasure includes rejection/fail/div and the release observer none.
`GExp_ReadPrefix.retained_reads` and `GExp_NativeBounds` account for native
rejected/failed prefixes and attempted syscalls, not only successful runs.

`GExp_Experiment.program` is defined BEFORE choosing H: arbitrary oracle
adversary, complete TX1, adaptive chooseSecond consuming the actual saved
checkpoint reply, complete TX2. First rejection retains its prefix and skips
second submission. `GExp_GlobalBudget.budget` covers every H and every rejection
path under explicit uniform adversary-query hypotheses Q0 and Q1.

## Ledger delta and bound

| Row | Checked advance | Full endpoint status |
|---|---|---|
| L088 beyond site projection | Both complete child bodies reified and their logs composed on same cuts | OPEN: full SDK oracle-associated ChildConeJoin/global source/runtime instance absent |
| L157 canonicalJoin.verifier | Complete preparation association, full body logs and source experiment bounds | OPEN: byte-indexed raw accepted log equality absent |
| L159 StoredCarrierBinding | Fixed-before-H source experiment, same-pair successful evaluation | OPEN: whole physical carried-data/runtime/oracle binding absent |

Globally removed rows: **NONE**. Added endpoint assumptions/trust items: **NONE**.
The local preparation Associated requirement is derived, not renamed as a
security assumption. authenticated_S1 remains in the predecessor Outcome and
is owned by AuS1_. No other worker's source, global ledger or candidates changed.

Conservative native cost: TX1≤11350 (preparation115 included), TX2≤11235,
total22585. This exceeds the contract1161 envelope by21424. Repeated addresses,
preprocessing, adaptive second-submission queries and rejected prefixes are
charged. `GExp_CollisionBudget.replay_collision` adds ALL1040 replay queries:

    firstReads ≤ Q0+Q1+22585+1040
    collision mass ≤ 6*(Q0+Q1+23625)^2 / 2^256.

The old1161 collision envelope and restricted(Q+34)*B start charge are NOT
proved for this source experiment. No contract is changed and no100-bit claim
is made. The loose outer-loop bound charges288 per iteration rather than
proving the single terminal verification cost; tightening is future work.

## Non-vacuity, quantifiers and next deliverable

The complete source-body erasures are all-input/all-outcome; the exact native
log equations are success-conditioned. Partial-syscall rejection and literal
TX1 early rejection are checked in GExp_Nonvacuity. The added conclusions impose
no new acceptance restriction. A joint accepted fixture satisfying every
retained native/runtime/crypto hypothesis is NOT proved; inherited runtime
fixture evidence is not relabelled as kernel inhabitation.

The fixed-pair composition derives f/s from ONE accepted oracle world. Its
separate all-world resource envelope does NOT establish that these selected
cuts are the actual deployed cuts in every world. The general adaptive program
is fixed before H, but its physical account/SDK/runtime association is still
absent. No arbitrary runtime is defined equal to this program merely to claim
StoredCarrierBinding. Likewise source acceptance is not equated to Port1's
raw byte verifier without its ordered-log refinement.

Next concrete deliverable: reify the containing SDK/account caller into the
same global source Program, derive f/s as response-driven outputs from original
byte submissions, and prove original C1/C2/folded-row30 frame occurrences on
that same log. Then derive the restricted(Q+34) start charge, apply charged
canonical replay recovery and prove the raw byte-indexed Port1 join. The actual
runtime must bind all carried data/history in the same oracle world. These
remain source-refinement obligations, not new cryptographic assumptions. The
existing loose native resource bound can be tightened by charging the single
terminal P6 verification once per tree rather than once per outer iteration.

## Validation, trust and artifacts

`GExp_final-audit.json` maps all70 CURRENT prefix modules to successful exact
source snapshots; all100 charged attempts have configurations and either full
receipts or an explicit prelaunch explanation. Actual invocations:78 successes,
19 failures,0 timeouts,0 memory kills;3 prelaunches. No unchanged timed-out or
memory-killed rerun, cap increase, package replay, full frozen manifest, Rust,
Kani or SBF gate was run. Six unchanged missing dependencies were built in the
coherent SInt2 workspace, with its pinned SdkC_/SdkD_/canonical objects reused.
No launcher/monitor/admission infrastructure was changed.

Every actual invocation used existing S2W launchers and `lake env lean -j1
-M7000 -DElab.async=false` in systemd scopes MemoryHigh6G/MemoryMax8G/SwapMax0/
TasksMax64. All swaps0; maximum peak RSS5235696KiB. Initial and final scope
inventories show only init.scope, and no GExp job remains live. Per-attempt
JSON records exact target/command, revision anchor+dirty flag, sourceSHA,
direct selected-object/sidecar hashes, status/wall/RSS/swap/cgroup and full
axioms lines. Failed receipts may print sorryAx because Lean recovered from
errors; they are excluded and every current source has a successful match.
No source contains sorry/admit/axiom/native_decide or depth/heartbeat overrides.

Final `GExp_Audit.lean` /100: exit0, wall1.8546395209850743s,
peakRSS5196356KiB,swap0, revision anchor6c3edffee3 with dirty source snapshots.
All ten audited endpoint/trace/budget/non-vacuity prints use only
[propext,Classical.choice,Quot.sound]. Every new theorem has its own axioms
print in its successful receipt. Static exact-hash and hypothesis comparisons
and git diff --check pass. This is focused verification on the pinned cache,
NOT a fresh release dependency rebuild or source-to-ELF proof.

No shipped or cfg(kani) file changed, so the ELF rebuild trigger did not apply.
Inherited pins, NOT newly rebuilt/revalidated:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Only GExp_ source modules and this receipts directory were edited. No session A
live worktree/candidates, WAdm_/PAln_/AuS1_ sources, global premise ledger,
wallet/account keys, funds, binaries/objects/ELFs/archives or release parameters
were changed. Stage commits are local; no push. The release target remains
unchanged and not established.
