#!/bin/bash
# generates PRVEq_CallerPrepTx1DeployedNOC_o1.lean from the P3o deployed file (namespace renamed) + NOC-seed section
cd "$(dirname "$0")"
S=../prov-p3o-20261110/PRVEq_CallerPrepTx1Deployed_o1.lean
O=PRVEq_CallerPrepTx1DeployedNOC_o1.lean
n=$(grep -n '^#print axioms bound' $S | cut -d: -f1)
head -$((n-1)) $S | sed -e 's/namespace PCVO_C/namespace PCVP_C/' -e 's/^import NNH_Tx2SourceConfiguration/import NNH_Tx2SourceConfiguration\nimport NOC_Run5bHost\nimport NOC_PrepareFront/' > $O
cat >> $O <<'EOT'

/-! ## Corrected seed: the headline's host context NOC_HostCtx / NOC_HostSeed.m0

Seed-generic: `generic_prepare`/`generic_tx1` take any Ops with the six Bound constant fields, so the statements
below hold for the Ops `currentInstalled (NOC_HostCtx.configuration c)` of every host context `c`, hence for every
`(NOC_HostSeed.m0 reserved)` and any later re-instantiation of the seed whose six constant fields are rfl-equal. -/
abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  DrvC_Installation.currentInstalled (AspisR1.NOC_HostCtx.configuration c)

theorem noc_prepare {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf (curN c)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (curN c) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem noc_tx1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.tx1 (xOf (curN c)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (curN c) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H

/-- Seed-generic over the uninstalled seed `m` (any NOC_HostSeed-like seed). -/
theorem seed_prepare (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C.verifier.candidate.prepare (xOf (cur m env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur m env err r) H :=
  deployed_prepare _ _ _ _ H

/-- Non-vacuity at the corrected seed: the installed op1 is NOC_HostSeed.filled (not the divergent residual). -/
theorem noc_op1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    @AspisR1CurrentCaller.Ops.op1 (curN c) = @AspisR1.NOC_HostSeed.filled (NNH_HostCtx.envOf c).reservation := rfl

/-- On a granted reservation op1 returns Ok (zeros n); cited from NOC_PrepareFront.filled, not re-proved. -/
theorem noc_op1_filled {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Std.Usize)
    (granted : (NNH_HostCtx.envOf c).reservation = true) :
    (curN c).op1 core.marker.CopyU8 n 0#u8 = ok (.Ok (AspisR1.NOC_PrepareFront.zeros n)) :=
  AspisR1.NOC_PrepareFront.filled c n granted

theorem noc_op1_ne_div {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Std.Usize)
    (granted : (NNH_HostCtx.envOf c).reservation = true) :
    (curN c).op1 core.marker.CopyU8 n 0#u8 ≠ Result.div := by
  rw [noc_op1_filled c n granted]; intro h; cases h

/-- Contrast: at the old NNH_HostSeed.m0 the same slot is the divergent residual. -/
theorem old_op1_div (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (n : Std.Usize) (x : Std.U8) :
    (cur NNH_HostSeed.m0 env err r).op1 core.marker.CopyU8 n x = Result.div := rfl

#print axioms noc_prepare
#print axioms noc_tx1
#print axioms seed_prepare
#print axioms noc_op1
#print axioms noc_op1_filled
#print axioms noc_op1_ne_div
#print axioms old_op1_div
end PCVP_C
EOT
