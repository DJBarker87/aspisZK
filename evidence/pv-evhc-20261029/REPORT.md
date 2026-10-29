# Fixture consumer aggregation preflight

**BLOCKED before admission: the two pinned dependency cohorts conflict.** No Lean process ran, no attempt ID was consumed, and the single authorized 16 GiB compile remains unspent. This is a dependency-cohort finding, not a theorem counterexample or an elaboration failure. The privacy target is not yet established.

Branch: `codex/pv-evhc-20261029`. Source revision: `b51b1040f2ffda4a6370a15ea71e5783a16bfa11`. Exact target: `PV_EVH_FixtureConsumer`, source `lean/PV_EVH_FixtureConsumer.lean`. The very first command checked SHA-256 `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`; the final check matches. The source was not edited.

The current user instruction explicitly overrides the older `AGG16-REQUEST.json` worker-launch prohibition, Stream A reuse prohibition, and 12G MemoryHigh setting. Requested scope: MemoryHigh=14G, MemoryMax=16G, MemorySwapMax=0, TasksMax=64, Lean `-M15000`. The remaining (h6) conditions are explicit requirements of the current instruction. No cap was raised, no source substituted, and no Stream A object rebuilt.

## Actual preflight evidence

The lead-owned runners were read only and SHA-256 checked twice, with identical results:

| Runner | SHA-256 |
| --- | --- |
| reservation_agg16.py | d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f |
| S2W_lean_host_agg16.py | 9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd |
| S2W_run_host_agg16.py | 8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6 |

Created `/home/dombarker/project-offloads/codex-pv-evhc-20261029/`. No writes were made to either predecessor cache. `verify_cohorts.py` performed streaming SHA-256 reads only. `host-hash-audit.json` records 22,433 successful checks: 6,374 event-cohort entries, 16,057 NDR transitive entries, and the NDR source/output pair. No host file differed from its own committed pin. Audit wall time: 29.803350855 seconds. This was not a compilation or release replay.

NDR authority: `06f74c902f`, `lean/NDR_CombinedAudit.lean`, git blob `b527950aa5e0f45c7e6921fd38d883a4eafc53ed`, SHA-256 `fdfd7c55f0b99a38a588bd0730878534f697d7f0e872e1529a4c89b560aeb794`. Its object matches `6ac4f024a9bd05672ac5e6b0ab20b73f9f6a919a74e85344654cb7787be5938b`. The copied `NDR_FINAL_COHORT_PINS.json` and `NDR_FINAL_OUTPUT_PINS.json` are taken directly from that revision. Event pins come from the committed `prepare-PV_EVH_Deployed.json` closure and successful `receipt-70400.json` through `receipt-70411.json` in the inherited evidence. The EVH preparation record carries the source-resolution evidence for project modules and the coherent privacy external-manifest checks.

`cohort-overlap.json` identifies **118 unequal object hashes** among **6,002 common module names**; 5,884 agree. Both sides of every conflict were independently read and match their respective manifest. All conflicting module names, paths and both hashes are retained. For example:

| Module | Event cohort SHA-256 | NDR cohort SHA-256 |
| --- | --- | --- |
| AeneasMeta.Extensions | f582f735bdd4f965977df7350789248c45665874aa3c510699b9238732dff113 | d4c7b9386b70ced61f8444bfba438bd29b20ce89ccd29edad3d32fb2c095e343 |
| Aeneas.Std.Primitives | 8991333b6bb5cf1070bf50689a7c2a2c329ed5d7bbd98f3c51d60e3e451a2d92 | 0ceb1684b620fd518e56633690ddaf802c253a619ff18817aa52c68f03084943 |
| Mathlib.Data.ZMod.Basic | 98137eb622dea253b91ef468523ef9a57ccb93545ac1b6e5109ab553adc6394b | 0598740d212f37ce0e8fb28030f09909e85158caba6d92b980b4e91b149e1901 |

These are transitive cohort fingerprints, not merely different disk paths. Taking event objects first would change the NDR dependency fingerprint; taking NDR objects first would change the event fingerprint and replace external objects governed by (h4). Ruling (h6) does not permit either substitution. The NDR recorded LEAN_PATH is its private objects directory plus the v4.32.0 sysroot. The event cohort records its event/caller/decoder/runjoin private directories plus the coherent external directory. No combined path has been validated. Both use Lean v4.32.0; the host Lean executable SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.

No exceptional source-resolution rule was invoked: no source edits, proof-only variant substitution under (h5''), h7 regeneration, or new source/model binding claim. own-1, own-2''' as an influence-channel principle, b3p6-1 and rdea-1 remain unchanged; this preflight discharges none of them. No allocator/runtime/compiler premise is converted into trust or claimed proved.

## Compile and axioms receipt

| Field | Result |
| --- | --- |
| Exact compile target | PV_EVH_FixtureConsumer |
| Small preflight compiles | 0 of at most 6 |
| Large compiles | 0 of exactly one authorized attempt |
| IDs consumed | none; restricted block remains 70700–70799 |
| Admission | not requested after cohort verification failed |
| Compile exit / wall / peak RSS / swap | unavailable: no compiler launched |
| New full consumer #print axioms | unavailable: consumer not elaborated |

No prior admission snapshot was used as permission to launch. The reservation script must still run immediately with any future launch, with allowed:true **and** exit 0, and the full refusal cooldown applies. No refusal, cooldown bypass, rule-(t) slip, failed-source resubmission or unchanged large retry occurred. The runner's guard was inspected but not invoked; `verify_cohorts.py` is not a Lean launch wrapper. Do not mistake these null compile metrics for a successful receipt.

The full **reused**, predecessor audit of the theorem this consumer applies is:

```text
'AspisR1.NDR_CombinedAudit.sourceOnHeadline' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`NDR_FINAL_RESULT.json` records that prior run as NDR_A001, exit 0, wall 5.142313743010163 seconds, peak RSS 8,282,464 KiB, swaps 0, source revision `6a157d7757046c5381438a07888844117957d997`, with the same frozen NDR source hash. Those metrics belong to NDR, **not this consumer**. The requested four consumer `#print axioms` commands remain unexecuted; no inference from the predecessor is reported as a new axioms result.

## Statement audit and limits

`public_fibre` supplies a model witness at the byte-handle caller statement through `caller_witness`. Its underlying caller-public equality connects the modeled lane index/frontier and request payment to the pinned transfer-13 record. It does not establish native decoder/handle association or universal live-request reachability.

`two_transaction_nonvacuity` applies `sourceOnHeadline` symbolically. Its conclusion uses one saved vector for both TX1 worlds, exactly the headline-installed SDK for all three calls, the pinned checkpoint bytes and length 1768, and TX2 acceptance. The two TX1 heaps remain different named posts; no equality between them is asserted. The explicit `FixturePdaRuntime base` premise is retained.

`instance_nonvacuity` packages those same three call results through `deployedInstance`; it does not prove a new runtime law. `FixturePdaRuntime base` says precisely that `base.op38` agrees with `JHs_PDA.derive` on the seven enumerated fixture calls. Its documented ABI, readable/disjoint memory and compute admission conditions remain required. It is an explicit hypothesis, not an axiom or a newly adopted trust item.

Under ruling (v), these conditional fixture statements must not be counted as an unconditional witness for the full event headline's conjunction of links. The existing model satisfiability result is distinct from an actual deployed instance. **The fixture witness does not prove the event acquisition or joint simulation links.** Native trace acquisition, template/handle association, source/provider association, allocation/abort conditions and compiler boundary obligations remain. No premise was removed, added, or changed in this task.

The exact final frozen source statements follow. They are source-audited, not newly kernel-checked in a combined environment.
# Exact frozen consumer statements

Source: `lean/PV_EVH_FixtureConsumer.lean` at `b51b1040f2ffda4a6370a15ea71e5783a16bfa11`, SHA-256 `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`. These are source statements, **not newly elaborated results**. Names resolve in namespace `PV_EVH_FixtureConsumer`, with the source's `open` directives.

### `public_fibre`

```lean
theorem public_fibre (handle : PV_RJ4IDB.Bytes) :
    ∃ w : R1Z.PV_RJDec_V047.H.Instance,
      R1Z.PV_RJDec_V047.H.public w = (deployedStatement handle).1
```

### `two_transaction_nonvacuity`

```lean
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
```

### `instance_nonvacuity`

```lean
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

## Retained fixture premise

```lean
def FixturePdaRuntime (base : Ops) : Prop :=
  ∀ seeds program, Call seeds program → base.op38 seeds program=JHs_PDA.derive seeds program
```

## Handoff

The next deliverable is a lead-approved coherent dependency cohort for both imports, including a reconciled external-object manifest and recorded complete dependency fingerprints. Merely allowing Stream A reuse does not establish hash equality. The 118 conflicts include immutable external library objects, so the six-small-dependency allowance does not authorize repairing this by rebuilding or substituting them. Once the cohort is coherent, check the unchanged consumer hash, runner hashes and failed-source guard, then perform fresh compliant admission and the single authorized compile. Capture all four full consumer axioms outputs then. No further compile was attempted here.

Only `evidence/pv-evhc-20261029/` changed. No push. The path-limited commit is listed in `COMMITS.txt`.
