# LOG D560 single aggregation compile and combined audit

Branch: `codex/pv-evhc-20261029`. Compiled source revision: `4e16fc7039e90c94bdf542e9c4c823f0955dee00`.
Worktree: `/Users/dominic/ZK/.worktrees/pv-evhc`.

The one authorized full-consumer compile **succeeded**. The subsequent raw combined audit **exited 1 and is incomplete**. No retries, dependency rebuilds, cap changes, or additional compiler launches occurred.

| ID | Target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| 90000 | `PV_BR_FixtureConsumer` | 0 | 6.470368635 | 8681176 | 0 |
| 90001 | `PV_BR_CombinedRawAudit` | 1 | 98.679940349 | 9674396 | 0 |

Both scopes used MemoryHigh=14G, MemoryMax=16G, MemorySwapMax=0, TasksMax=64 and Lean `-M15000`, `-j1`, `-DElab.async=false`. Each admission JSON says `allowed:true` and its recorded exit is 0. Both report zero already-reserved bytes. No refusal or cooldown occurred. The quiet marker had expired (until=1793588088, checked at 1793588280.833677); it was left untouched. `launch-preflight.json` records the ID scan, workspace hashes and failed-source guard hash.

## Pinned-input verification

`verification.json` records PASS for 52,505 checks and 16,652 module resolutions. `hash-checks.json`, `resolution.json`, and `local-source-checks.json` retain the individual checks. Verification preceded admission. Target source SHA-256: `48381d7a82300eadec1f5973cd87bd5b4119d1f399717d9210263e379ef1297e`. Every one of the 152 handoff source files matched locally. The 69 active private modules matched their object pins, current source, successful compilation source receipt and handoff source; active companions were inventoried. All NDR manifest objects and 3,116 recorded NDR source hashes matched, as did all reconciled cohort objects and recorded companions, using the first-root namespace resolver and exactly READY.json's LEAN_PATH. Stream A NDR final source/output pins also matched. No authoritative object was rebuilt or overwritten.

The initial checker mistakenly selected an old successful receipt in filesystem order for PV_BR_BuilderAdmission. Inspection established that current source matches successful attempt 78104, whereas unordered selection had chosen 78101. The checker was corrected to sort attempts. `verification-initial.json` and `preflight-correction.txt` retain this checker error. No actual pinned source/object hash mismatch, admission or compiler launch occurred during that initial check.

All three lead-owned agg16 runner copies matched their full hashes, both at the authoritative host paths and in the task directory:

- reservation_agg16.py: `d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f`
- S2W_lean_host_agg16.py: `9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd`
- S2W_run_host_agg16.py: `8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6`

`launch.py` enforces allowed:true AND exit 0, 180-second cooldowns and at most 20 admission checks. It refuses failed-source hashes and used attempt directories. Its hash is in launch-preflight.json. The lead-owned runners were copied byte-identically, not edited.

## Axioms evidence and limitation

`PV_BR_CombinedRawAudit.lean` imports the newly compiled consumer in the identical LEAN_PATH closure. It embeds the unchanged NDP.audit implementation from `research:evidence/native-axaudit-20261028/NDP_Audit.lean`, followed by 31 root calls and 31 #print axioms queries. `audit-method.json` pins the source and research revision. Each successful raw walk visits every reachable constant through actual kernel bodies, independently enumerates kernel/serialized axioms, and verifies equality with collectAxioms.

28 roots completed that raw walk and equality check, with only standard axioms. Raw walks for these three roots did not complete:

- `PV_EVH_FixtureConsumer.instance_nonvacuity`
- `PV_EVH_FixtureConsumer.two_transaction_nonvacuity`
- `AspisR1.NDR_CombinedAudit.sourceOnHeadline`

First error: `PV_BR_CombinedRawAudit.lean:95:0: error: missing reachable constant AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3`. The same missing constant caused all three errors. This is a missing-constant audit obstruction, not a memory kill. No repaired audit or retry was launched.

**Fallback evidence: #print axioms only.** All 31 #print axioms queries completed in both runs. They report only subsets of propext, Classical.choice and Quot.sound. These print results do not substitute for successful raw traversal of the three obstructed roots. The combined raw audit is not certified complete.

Full raw audit stdout is retained as `lean-90001/stdout.log.xz`, with the SHA-256 of all 91,781,168 original bytes in `lean-90001/stdout.log.sha256`; decompression/hash verification passed. Full per-run print results are also in `lean-90000/full-print-axioms.txt`, `lean-90001/full-print-axioms.txt` and both receipt JSONs. `RESULTS.json` contains all 28 raw results and all errors. `receipt-validation.json` verifies admission, source snapshots and output integrity; it does not claim the raw audit passed.

Full #print axioms output from the successful consumer compile:

```text
'PV_EVH_FixtureConsumer.deployedInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_EVH_FixtureConsumer.instance_nonvacuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_EVH_FixtureConsumer.public_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_EVH_FixtureConsumer.two_transaction_nonvacuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_BR_Transport.payment_left_inverse' does not depend on any axioms
'PV_BR_Transport.payment_right_inverse' does not depend on any axioms
'PV_BR_Transport.payment_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_BR_Transport.payment_injective' does not depend on any axioms
'PV_BR_Transport.tree_left_inverse' does not depend on any axioms
'PV_BR_Transport.tree_right_inverse' does not depend on any axioms
'PV_BR_Transport.tree_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_BR_Transport.tree_injective' does not depend on any axioms
'PV_BR_Transport.verifier_retraction' does not depend on any axioms
'PV_BR_Transport.verifier_join_split' does not depend on any axioms
'PV_BR_Transport.verifier_split_join' does not depend on any axioms
'PV_BR_Transport.verifier_embedding_injective' does not depend on any axioms
'PV_BR_Transport.verifier_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_BR_Transport.mapCoreError_inverse' does not depend on any axioms
'PV_BR_Transport.payment_result_transport' does not depend on any axioms
'PV_BR_Transport.tree_result_transport' does not depend on any axioms
'PV_BR_AdmissionTransport.prover_run_roundtrip' does not depend on any axioms
'PV_BR_AdmissionTransport.from_to' depends on axioms: [propext]
'PV_BR_AdmissionTransport.to_from' depends on axioms: [propext]
'PV_BR_AdmissionTransport.mapRunError_inverse' does not depend on any axioms
'PV_BR_AdmissionTransport.mapRunError_success' depends on axioms: [propext]
'PV_BR_AdmissionTransport.validateCommon_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'PV_BR_AdmissionTransport.validateCommon_success' depends on axioms: [propext, Classical.choice, Quot.sound]
'R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed' depends on axioms: [propext, Classical.choice, Quot.sound]
'R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'R1Z.PV_RJ4IDB_CallerLive.caller_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.NDR_CombinedAudit.sourceOnHeadline' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact final statements and retained premises

The pinned source snapshot `PV_BR_FixtureConsumer.lean` supplies the namespace, opens, deployedStatement and deployedInstance definitions. The three theorem statements below are copied verbatim from it (without proof bodies). In particular `FixturePdaRuntime base` remains explicit.

```lean
theorem public_fibre (handle : PV_RJ4IDB.Bytes) :
    ∃ w : R1Z.PV_RJDec_V047.H.Instance,
      R1Z.PV_RJDec_V047.H.public w = (deployedStatement handle).1

theorem two_transaction_nonvacuity
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second
        (AdapterRw.r1_pool_adapter.owned.stage2_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,()))

theorem instance_nonvacuity (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      (deployedInstance base stage slot).1 =
        ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      (deployedInstance base stage slot).2.1 =
        ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val = JFx_NativeBytes.checkpoint.val ∧ saved.val.length = 1768 ∧
      (deployedInstance base stage slot).2.2 = ok (.Ok (JHg_World.e2.heap,()))
```

This establishes elaboration of the staged full-consumer declarations against the recorded closure. No privacy premise was removed, added, weakened or changed. public_fibre is the caller's model public-fibre witness. two_transaction_nonvacuity and instance_nonvacuity establish the conditional fixture execution witness, retaining FixturePdaRuntime base; they do not establish arbitrary live reachability or native caller association. The fixture witness does not prove the event acquisition or joint simulation links. All existing native/runtime/simulation, deployment and side-channel conditions remain.

**Privacy target not yet established.** The next concrete deliverable is an explanation and correction of the missing reachable constant in this exact combined environment, with a changed-input, separately authorized raw audit. No further attempt is implied by this report.

No crate/program, staged theorem source, Stream A source, existing authoritative object, other worktree, wallet or account key was changed. Only the fresh consumer output was added in this branch's reused private object root, so the audit could load it through the exact pinned LEAN_PATH. `RESULTS.json` pins that output and its companions. Unrelated pre-existing pv-dup changes were left untouched. No push.
