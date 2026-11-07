import NNH_ModelConfig
import NNH_064Reservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_ModelLeafPorts
open Aeneas Aeneas.Std VTop_Stages
/-- The C06 model uses the SAME fallible reservation as its native source.
The width is the original constructor domain, not a new caller restriction. -/
theorem pending {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (sha : List RSL.Bytes → RSL.B32) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : RSL.Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) (err : E)
 (weights : Slice aspis_core.field.QM31) (width : weights.val.length=64) :
 NKE_CommonNative.pendingG r weights=
 Port3_NativePendingInstall.source (NNH_ModelConfig.configuration missing env err r).reserved weights := by
 have same : NJJ_Common.pending r weights=NKE_CommonNative.pendingG r weights := by
  have original := NKE_PendingNative.source r weights (NKE_CommonNative.zeros weights) width
   (by simpa only [NKE_CommonNative.zeros,List.length_replicate] using width)
  cases r with
  | Err e => exact original
  | Ok unit => cases unit; exact original
 unfold NJJ_Common.pending at same
 rw [NNH_064Reservation.tag sha pda clock r env rep] at same
 rw [NNH_ModelConfig.reserved]
 exact same.symm

/-- Canonical217 returned values at the actually selected SDK op50. This does
not reclassify the principal's native certificate or claim ledger acceptance. -/
theorem lane {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation) (b : Slice U8)
 (o : RSL.Obs (Except RSL.ProgramError RSL.LaneState))
 (value : Except RSL.ProgramError RSL.LaneState)
 (law : RSL.TX2_217.Ref (NND_Carrier.bytes b) env o) (ret : o.exit=.ret value) :
 NNH_ModelCarrier.outer (NND_Carrier.reply NND_Carrier.lane)
  ((NNH_ModelConfig.sdk missing env err r).op50 b)=.ok value := by
 rw [NNH_ModelConfig.lane]
 exact NNH_LaneModel.returned b env o value law ret
#print axioms pending
#print axioms lane
end AspisR1.NNH_ModelLeafPorts
