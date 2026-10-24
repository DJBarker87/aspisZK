# Port16CUT accepted handoff

Branch `codex/cx-port16cut-20261024`, assigned base `98e705b8ff`. Plan first
committed at `ef9bf4ad78`; proofs committed at `e6f9779348`. No merge/push.
The scoped actual-source control objective is green. Both deployed security
targets remain **not yet established**.

## Actual theorem and assumptions

`Port16CUT_Driver.stages` and `.rust` quantify over every Ops, reserved flag,
Unwrap, delegated Implementation rest, weight function w, digest type/instance,
hash, oracle H, and stage/input arguments. With only `LocalBudgets rest w`,
actual unchanged `Port1_Driver.stages/rust` interpreted using
`Port9OR_Installed.implementation ops reserved unwrap rest` has log length
at most `1046 + delegatedWeight w`, on every outcome. `.rust1161` additionally
requires `delegatedWeight w ≤ 115` and concludes log length ≤1161.

```
LocalBudgets rest w :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ [3,4,6,7,9,10,11,12,17,19] →
    (eval H (rest op)).1.length ≤ w (operationId op)

delegatedWeight w :=
  2*w3+w4+2*w6+w7+2*w9+2*w10+2*w11+w12+w17+w19
```

These are unrestricted per-operation bounds, not a whole-driver bound hidden
in a structure. No success, independent checkpoint, acceptance, output equality,
refinement, or reached-domain hypothesis is present. Concrete installed rest
and numerical weights remain uninstantiated producer obligations.

`Port16CUT_TX2.tx2` is now a standalone green theorem (lean-001). Its reader
and literal batch1 contribute 566; delegated contributions are
w3+w17+w11+w10+w6+w9+w19. Accepted Port15 TX1 contributes
480+w3+w4+w7+w12+w11+w10+w6+w9. These sum to 1046+delegatedWeight.
Both opaque-to-elaboration program cuts have explicit full result types,
proved equalities to the unchanged actual interpreted terms, and separate numeric
bounds. `next` uses the **same saved Vec returned by TX1**, passing saved.deref
to actual TX2; TX2's source-control proof retains actual reply Prepared and
accumulator arguments. Fail/div/inner rejection truncate the executed prefix.
Neither physical batch bodies nor P6 recurrence constants are unfolded.

## Before/after interface

Before, TX1 alone was green; TX2 existed only inside failed modules and no
whole-driver bound was accepted. Port6AUTH Accounting required arbitrary rust,
`Physical rust`, an unrestricted ByteProver P, `∀H, length(eval H P)≤Q`, and
`∀H i, length(eval H (rust i))≤1161`.

After, the concrete-driver `.rust1161` replaces that last whole-driver premise
with the explicit local operation bounds above and weighted≤115. No input,
H, outcome, or success quantifier was restricted. `Port16CUT_Accounting.budget`
uses existing `Port1_StoredCarrier.driver_physical` for this exact driver and
preserves arbitrary P and the same ∀H Q bound. It proves source first reads
≤Q+1161; `.log_length` proves **whole two-pass total** ≤Q+2322. Physicality
is proved by the reused theorem, not dropped. No query independence/freshness,
new metric, or collision-loss term is introduced.

## Validation and retained failures

Accepted module receipts:

| Attempt | Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| 001 | Port16CUT_TX2 | 0 | 3.989 | 4451544 | 0 |
| 005 | Port16CUT_Cuts | 0 | 2.094 | 4446252 | 0 |
| 006 | Port16CUT_Bind | 0 | 1.920 | 4429448 | 0 |
| 007 | Port16CUT_Driver | 0 | 5.245 | 4438944 | 0 |
| 009 | Port16CUT_Accounting | 0 | 1.991 | 4463464 | 0 |
| 010 | Port16CUT_Audit | 0 | 1.969 | 4447820 | 0 |

`lean-010/stdout.log` prints full explicit/unelided theorem statements, hidden
LocalBudgets, delegated IDs, weights, program cuts, next, unchanged Driver,
Physical, and the full axioms. Only propext, Classical.choice, Quot.sound occur
in accepted results. Each receipt retains exact target/command, source revision
and source hashes, selected dependency object hashes/paths, exit, wall/RSS/swap,
and full axioms. Source changes were dirty against the recorded git label;
the snapshotted source hashes are authoritative. `source-audit.json` assesses
all accepted source hashes and reachable local sources and validates admissions.

Attempts002–004 retain their exact source/logs: default 200000-heartbeat whnf
failure in cut-bound arithmetic. Merely changing equality transport did not fix
it. The successful replacement moves numeric facts into separate declarations
with only w in scope, so omega cannot inspect an evaluation hypothesis.
Attempt008 retains the missing FS firstReads namespace error and generated
sorryAx; it is **not adopted**. Attempt009 adds the namespace and is green.
All previous Port15 failed candidates remain untouched. No heartbeat/depth limit
was changed; no failed input was rerun unchanged.

Reviewed admission scanner/fixtures passed before work. All ten launches use
fresh complete-hierarchy admission under `/tmp/aspis-r0-lean.lock`, sum+8GiB<55GiB,
then an independently verified 6G high/8G max/zero-swap/TasksMax64 scope.
Exact launch construction is in `tools/port16cut-20261024/Port16CUT_compile.py`;
all individual reservation JSON and launcher logs are retained. System/Docker,
populated descendants, cap dedup, uncapped visibility and fail-closed missing
required data are covered. No full manifest or unchanged regression replay ran.

Reused Port15 Cost/Local/TX1, Port12 owned batch caps, writer/reader counts,
Port1 physicality and Port6 accounting are explicitly historical cached evidence.
`reused-port15-host-pins.json` pins sources and objects at
`/home/dombarker/project-offloads/codex-cx-port15driver-20261024`;
this path is added to the isolated Port16 LEAN_PATH. The source audit verifies
these match accepted source bytes and the imported TX1 object. No coherent
release closure or new ELF identity gate follows. Historical full aggregate
admission remains unverified.

## Budget and scope

Inherited 239 actual+1 preLean=240 charged. New10 actual (6 green,4 failed)=250/252
charged; **2 unused slots remain**, not reclaimed charges. Actual total249;
Kani0/20. Core and optional bridge are complete; no further replay is needed.
No local/cold Lean, Rust/arithmetic/extraction/ELF/SBF/runtime build, shared
service/tool, shipped source/backend/protocol/trust/security-contract change.
No key was touched. `VTop_Flow` and `Port1_Driver` are byte-identical to base.

Next producer: concrete installed delegated source bounds and weights≤115,
recorded in NEXT-PRODUCER.md for root A. Parser/prepare7, powers17, sampler,
primitive/S6/S10 frontier remains unchanged. Acceptance→recovery/parse/query/
root/frame/no-hit, CleanAcceptedModel, StoredCarrierBinding, terminal classifier,
primitive adoption and release identity remain independent open obligations.
Security expression unchanged: (Q+34)*B+kappa(Q+1161)+2^-126+2^-454.
