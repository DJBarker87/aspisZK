NNQ host O2 partial handoff. Branch codex/cx-dgo-host-20261107, base953e3af13bb.
Target not yet established. This job delivers items1-7 only, not O2.

| Recipe item | Status and exact Lean name | Accepted receipt |
|---|---|---|
|1 split|CLOSED AspisR1.NNQ_HostDigest.split|NNQ_L001|
|2 SDK|CLOSED AspisR1.NNQ_HostDigest.sdk_withDigest|NNQ_L002|
|3 observer|CLOSED AspisR1.NNQ_HostDigest.observe_op43|NNQ_L010|
|4 trace simulation/lowering|CLOSED AspisR1.NNQ_HostDigest.CallSim, Sim, lowerN_sim|NNQ_L013|
|5 outer stages|CLOSED AspisR1.NNQ_HostDigest.first_decoded_sim, stage1_sim, stage2_sim|NNQ_L016, NNQ_L020|
|6 preparation|CLOSED AspisR1.NNQ_HostDigest.DSim, lowerP_dsim; AspisR1CurrentCaller.S1PrepareCode.NNQ_Port.dictionary_irrelevant|NNQ_L021,022,024,026,028|
|7 batch|CLOSED AspisR1.NNQ_HostDigest.batch_eq, batch_stage_eq|NNQ_L030|
|8 first/second child code|OPEN exact GExq_FirstCode.code/GExq_SecondCode.code dictionary equalities, uncompiled proposal NNQ_FirstCode.lean.txt|No launch|
|9 child execution|OPEN CallSim transport through GExq_ChildCode.execute; depends on8|No launch|
|10 account/O2|OPEN account_withDigest and exactly DGP_HostDigest.O2; depends on9|No launch|

The OPEN goals and dependency-by-dependency continuation are in
../dgo-host-20261108/NNQ_REMAINING.md. There are no Kani-dependent remaining members. Budget is
30/30 actual scopes,16 exit0 and14 rejected;0 Kani/0 extraction. Limits on
EVERY launch:6G high/8G max/swap0/tasks64,-j1 -M7000 async=false,timeout180.
Each admission allowed=true AND exit0; each preflight disk>=40GB and host share
count<6. No memory kill, wall timeout, or raised cap/heartbeat/recursion option.
Failed snapshots/diagnostics remain archived and receive no proof credit.

All accepted new theorem audits are subsets of propext,Classical.choice,
Quot.sound. The final NNQ_COMBINED_IMPORT includes NNH_ContinuationCombined,
NNH_S5FocusedHost, unchanged DGP_HostDigest and every accepted NNQ module
transitively. Item7's six declarations live IN that final module after the
standalone wrapper's let-bound rewrite was corrected. L030 exit0,4.474146s,
6707244KiB RSS,swap0,source revision2e05d7cb19c (dirty exact source hash in
receipt);15 printed roots standard-only. Full AGENTS section6 fields are in
NNQ_COMPILE.tsv and each NNQ_L*/receipt.json/time.log/stdout.log; no final
release/manifest replay is claimed.

Prepend for NNH_:
/home/dombarker/project-offloads/codex-cx-dgo-host-20261108/NNQ_objects
then the unchanged NNH run5 path:
NNH_R4_objects:NNH_objects:NNH_seed:NNH_library_seed beneath
/home/dombarker/project-offloads/codex-cx-integrate-20261111.
Toolchain leanprover--lean4---v4.32.0. Do not import the .lean.txt proposals.
Own generated sources/accepted objects are retained for the consumer; no shared
NNH source or object was written. Redundant own scratch inputs are removed.

Old/new SHA256s: ../dgo-host-20261108/NNQ_PINS.json records old=null for every new source and its
accepted new source/object hash, selected dependency hashes including resolved
Aeneas/AeneasMeta objects, and equal old/new hashes of DGO_HOST_RECIPE,
DGO_O2 and DGP_HostDigest. Receipt source revisions remain historical exact
launch revisions rather than this final documentation commit. No shipped
source or ELF changed, so no three-ELF rebuild trigger. No trust change,
axiom, sorry, native_decide, new premise, adversary/hashv/H restriction, ledger
credit or headline-bound credit.

Next consumer: NNH_RecordedCharge.bound transported by O1 and O2, followed by
actual-experiment pointwise failure inclusion. O1 archive correction is noted
but NOT recompiled. Condition(4) strategy is owner-approved and RECORDED,
NOT proved. The three O2 hypotheses and its complete statement are unchanged.
No real host counterexample to O2 was established. Final read-only host
check verified16 accepted modules and3846 dependency occurrences
(NNQ_HOST_FINAL_CHECK.json).

O2 statement, quoted verbatim from DGP_HostDigest.lean section3 (unproved):

```lean
def O2 : Prop :=
  ∀ (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (env env' : RSL.Env) (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (a : SCE_Experiment.Adversary Bool) (Q : Nat),
    env.pda = env'.pda → env.clock = env'.clock → env.reservation = env'.reservation →
    NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env) env) err r)
        err r hashv a Q =
      NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env') env') err r)
        err r hashv a Q

```

target not yet established
