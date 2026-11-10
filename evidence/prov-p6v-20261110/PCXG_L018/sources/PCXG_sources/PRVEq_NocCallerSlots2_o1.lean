import NOC_Run5bHost
import NOC_Tx1Forward
import NOC_Tx1Conv
import NOC_ConvLeaves
import NOC_Conv094
import NOC_Op9
import NNX_PreparedValue
import NNH_Run5bCurrentExpand
import NNH_Run5bCurrentPending
set_option autoImplicit false
noncomputable section
/-! PCVP_ second batch: op8, op10, op18 forward correspondences at the corrected seed, and an axioms audit of the
existing theorems cited as the coverage of op1, op3-op7, op9, op11 and the converses (those are already stated at
the NOC configuration, `NOC_PrepareFront.cur c`, or are seed-generic in `m`). -/
namespace AspisR1.PCVP_NocSlots2
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NNH_Libraries

abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  DrvC_Installation.currentInstalled (NOC_HostCtx.configuration c)
abbrev M {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation

/-- op8 Prepared::new: library prepare value ok => installed op8 returns the carrier image (NNX_PreparedValue.source). -/
theorem op8 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (sem : RSL.Verified LIB_VLib.library)
    (v : LIB_VCarriers.View) (g after : LIB_VCarriers.E29) (p : LIB_VCarriers.Prepared)
    (called : LIB_Prepared.value (sem, v, g) (NNH_HostCtx.envOf c) = (.ok p, after)) :
    (curN c).op8 (NNV_PreparedAtHost.digest c) (NNV_PreparedInputs.sem sem) (NNV_PreparedInputs.view v) ()
      (NNV_PreparedInputs.scratch g) =
    .ok (.Ok (InstalledPreparation.currentPrepared p), NNV_PreparedInputs.scratch after) :=
  NNX_PreparedValue.source c sem v g after p called

/-- op10 expand_semantic: installed = LIBC_ExpandSemanticModel.output on 7015 -> 13831 byte windows. -/
theorem op10 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (src dst : Slice U8)
    (ns : src.val.length = 7015) (nd : dst.val.length = 13831) :
    (curN c).op10 src dst = .ok (.Ok (), LIBC_ExpandSemanticModel.output src) :=
  NNH_Run5bCurrentExpand.semantic (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation src dst ns nd

/-- op18 BatchedWeights::new: library weights ok => installed op18 returns the pending carrier. -/
theorem op18 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : VL.Acc) (pending : VL.Weights)
    (width : a.weights.val.length = 64) (called : LIB_VLib.weightsNewValue a (NNH_HostCtx.envOf c) = .ok pending) :
    (curN c).op18 (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref =
    .ok (.Ok (Tx1Q_Carriers.unPending pending)) :=
  NNH_Run5bCurrentPending.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation a pending width called

#print axioms op8
#print axioms op10
#print axioms op18
-- audit of the cited existing theorems (names must exist in the replay closure)
#print axioms NOC_PrepareFront.filled
#print axioms NOC_PrepareFront.values
#print axioms NOC_Tx1Forward.batch
#print axioms NOC_Tx1Forward.query
#print axioms NOC_Tx1Forward.source
#print axioms NOC_Op9.op9
#print axioms NOC_SeedTransfer.op9
#print axioms NOC_SeedTransfer.current
#print axioms NOC_SeedTransfer.sdk
#print axioms NOC_ConvLeaves.filled
#print axioms NOC_ConvLeaves.parse
#print axioms NOC_ConvLeaves.view
#print axioms NOC_ConvLeaves.prepared
#print axioms NOC_Conv094.scan
#print axioms NOC_Conv094.geometry
#print axioms NOC_Conv094.accNew
#print axioms NOC_Conv094.weightsNew
end AspisR1.PCVP_NocSlots2
end
