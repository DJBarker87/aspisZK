DGO host instantiation handoff, completed by NNQ continuation.

Items1-7 CLOSED as recorded in ../dgo-host-20261108/NNQ_L001-L030: split; sdk_withDigest; observe_op43; lowerN_sim; first_decoded_sim/stage1_sim/stage2_sim; lowerP_dsim/NNQ_Port.dictionary_irrelevant; batch_eq/batch_stage_eq. These accepted objects and their hashes were reused unchanged.

NNQ host O2 continuation. Branch codex/cx-dgo-host-20261107.

Items1-7 retain the original accepted NNQ_L001-L030 receipts and NNQ_COMBINED_IMPORT. The continuation closes:

| Item | Lean name in AspisR1.NNQ_HostDigest | Receipt |
|---|---|---|
|8|firstCode_eq, secondCode_eq; prepare_lower_eq, secondCommon_eq|NNQ_L031|
|9|child_sim; child_raw_sim for raw stage composition|NNQ_L032,034|
|10 account|caller_first_eq, caller_second_eq; firstSyntax_eq, secondSyntax_eq, account_withDigest|NNQ_L035,036|
|10 recorder/O2|observer_withDigest; o2 : AspisR1.DGP_HostDigest.O2|NNQ_L037,038|

O2 is proved with exactly the existing three hypotheses. Its statement is quoted verbatim in NNQ_O2.lean. No source/trust/model change, new premise or restriction of adversary/hashv/H. Standard axioms only: propext, Classical.choice, Quot.sound. No shipped files changed; inherited ELF pins are default f8c0ec72…, devnet63ad3e9c…, Pool e0e49c34… (owner amendment); no rebuild trigger.

NNQ_L033's memory-exhausted combined shape was split, then its replacement passed at L034/L035. No failed shape was rerun unchanged. Every launch used the unchanged 180s timeout, -j1 -M7000 async=false and a systemd scope (6G high,8G max,swap0,tasks64), fresh allowed:true/exit0 admission, whole-host scope count<6 and disk>=40GB. Exact target, source revision/hash, dependency fingerprint, exit, wall, peak RSS, swap and printed axioms are in NNQ_COMPILE.tsv and each receipt.json/stdout.log/time.log. NNQ_L038: exit0,4.271607455s,6703972KiB RSS,swap0; source revision fb3108aa636 with exact dirty source hash in receipt.

For NNH run6, prepend /home/dombarker/project-offloads/codex-cx-dgo-host-20261108/NNQ_objects to NNH_R4_objects:NNH_objects:NNH_seed:NNH_library_seed under /home/dombarker/project-offloads/codex-cx-integrate-20261111. Toolchain v4.32.0. NNH run5 workspace and objects were read-only. Final NNQ_COMBINED_IMPORT2 passed NNQ_L039: exit0,3.929073355s,6667172KiB RSS,swap0; source revision cf6512bd6e5 with dirty exact source hash in receipt. It imports every accepted NNQ module and audits all14 new roots (standard axioms only). NNQ_PINS.json records accepted source/object hashes and all selected dependency pins, including the resolved Aeneas library. NNQ_HOST_FINAL_CHECK2.json verifies24 accepted overlay modules and271 unique object/dependency files read-only. NNQ_validate.py checks all39 historical/continuation receipts, admission, caps, scope share, disk, source hashes and accepted axioms. No full frozen-release manifest replay is claimed.

Remaining integration: NNH_RecordedCharge.bound transported using O1/O2; same-world actual failure inclusion, condition(4), and the deployed headline. No NDT/headline credit. See NNQ_REMAINING.md. Continuation budget9/20 scopes (8 pass,1 memory rejection),0 Kani/0 extraction. Items8,9,10 are each CLOSED; no assigned member remains to attempt, so the job ends below80% with all requested proofs and final import complete. Old receipts remain historical; no repeated unchanged regression. Stage commits local; no push.


O2 statement, quoted verbatim from DGP_HostDigest.lean section3; proved by AspisR1.NNQ_HostDigest.o2:

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
