# PCVP_ HANDOFF: phase P3p (corrected-seed restatement, install-wrapper correspondences)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; no trust row added; nothing pushed or merged. Branch codex/pc-prov-p3p-20261110. Frozen source 4bb3b3f. Lean scopes 13 of 45 (PCVP_L001-L013), extraction 0, one at a time, caps 6G/8G unraised, swap 0, peak RSS 6.8 GiB, verified scopes 3-7 s. Summary: PCVP_STATUS.json.

## Difference at a matching configuration
None found. Observation: at NNH_HostSeed.m0 the installed op1 is `div` (PCVP_C.old_op1_div); at the corrected seed it is NOC_HostSeed.filled (NOC_PrepareFront.filled gives Ok(zeros n) on a granted reservation). P3o deployed_prepare/deployed_tx1 at NNH_HostSeed.m0 are not credited.

## Claims (exit-0, standard axioms only, no sorry/axiom/native_decide; PRVEq_*_o1 copies carry the Aeneas-default maxHeartbeats 1000000 unchanged)
1. Corrected seed prepare/tx1: PRVEq_CallerPrepTx1DeployedNOC_o1.lean (L003): noc_prepare, noc_tx1 at currentInstalled(NOC_HostCtx.configuration c) for every host context; seed_prepare generic in the Uninstalled seed; non-vacuity theorems noc_op1, noc_op1_filled, noc_op1_ne_div; old_op1_div contrast. Conditional on the six Bound constant fields, which hold by rfl at the deployed Ops: organisation.
2. model1/model2: PRVEq_AdapterStage{1,2}DeployedNOC_o1.lean (L005, L007): noc_model1, noc_model2 at NOC_HostCtx.sdk c. Stage1 Bound is rfl for every Ops. noc_model2 uses hashv := LIB_Env.hashv (envOf c); identification with NOC_HostCtx.hashv c (DGP_HostDigest.hashvInst) is not claimed.
3. Install-wrapper correspondences (library model only): PRVEq_NocCallerSlots_o1 (L009: op3,4,5,7,16,17,19,20, cur_eq) and PRVEq_NocCallerSlots2_o1 (L010: op8,10,18, plus axioms audit of 17 cited NOC_ theorems). These restate existing NNV_/NNH_ theorems at the corrected seed (m := NOC_HostSeed.m0, defeq to the NOC configuration, probe L008); no new mathematics. op1/op6/op9/op11 are covered by existing theorems already stated at the NOC configuration (cited in PCVP_UNRELATED.json).
4. Compositions: PRVEq_NocStage1Compose_o1 (L011) fresh_stage1_iff: fresh frozen stage1_owned at the headline sdk Ok-iff library tx1Value (with NOC_Stage1Iff.iff345). PRVEq_NocPrepTx1Compose_o1 (L013): fresh_prepare_forward/converse, fresh_tx1_forward/converse (existing NOC_PrepareFront/PrepareConv/Tx1Forward/Tx1Conv carried to the fresh frozen definitions via item 1).

## What this is not
No deployed slot is related to the frozen emission of its callee: all correspondences go to the library model. The frozen-emission relation is the PCXD gate status, unchanged. The 14 stage2 adapter slots (op22,23,20,16,17,11,50,52,49,48,51,45,53,44) have no per-slot theorem here (tx2 evidence dirs not inspected); stage1 op21/24/47 only via the whole-function Ok-iff. See PCVP_UNRELATED.json, PCVP_REMAINING.json.

## Failed shapes / process
L002: type mismatch in noc_op1 as first stated ((curN c).op1 with implicit arguments); fixed by the @Ops.op1 form (L003). I removed the L002 receipt directory by mistake; the failure remains in PCVP_ATTEMPTS.jsonl. No shape failed twice. No scratch with sorry exists. The probe PRVEq_Probe_p1.lean (L008) is committed (no sorry).
