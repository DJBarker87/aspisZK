import NHV_InactivePacket
import NHV_PendingPacket
set_option autoImplicit false
noncomputable section
namespace NHV_NativeOps
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev TopOps := VTop_Stages.Ops
/-- Only now-packetized producer fields are installed; NFU resume, Merkle and
NHM finish remain the exact named fields of base. -/
def producers (base : TopOps) (reserved : Bool) : TopOps :=
 {base with
  op2 := NHV_InactivePacket.packet
  op10 := Port3_NativePendingInstall.source reserved
  op11 := Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted}

def installed (base : TopOps) (qbase : Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) : TopOps :=
 NHT_PacketOps.installed (producers base reserved) qbase qPlace gPlace

theorem source (base : TopOps) (qbase : Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool)
 {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
 NHT_EmittedCommon.tx2_common (installed base qbase qPlace gPlace reserved)
   D pub proof checkpoint hash obs =
 VTop_Stages.verifier.candidate.tx2_common (installed base qbase qPlace gPlace reserved)
   D pub proof checkpoint hash obs :=
 NHT_PacketOps.source (producers base reserved) qbase qPlace gPlace D pub proof checkpoint hash obs

theorem slots (base : TopOps) (qbase : Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) :
 (installed base qbase qPlace gPlace reserved).op2=NHV_InactivePacket.packet ∧
 (installed base qbase qPlace gPlace reserved).op10=Port3_NativePendingInstall.source reserved ∧
 (installed base qbase qPlace gPlace reserved).op11=
   Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted ∧
 (installed base qbase qPlace gPlace reserved).op17=NHT_PacketOps.powers ∧
 (installed base qbase qPlace gPlace reserved).op9=Port3_FlushInstall.flush :=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem pending_reply (base : TopOps) (qbase : Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) :
 (installed base qbase qPlace gPlace reserved).op10 a.weights.deref =
 if reserved then ok (.Ok (NFW_QueryResume.pending a)) else ok (.Err .Allocation) :=
 NHV_PendingPacket.source reserved a width

/-- Forgetting an unchanged state/empty trace preserves all Result constructors. -/
def forget {A : Type} (r : Result (A × Unit × List Unit)) : Result A := do
 let out ← r
 ok out.1

theorem forget_run {A : Type} (r : Result A) :
 forget (NEB_PureFrame.run (Event:=Unit) () r)=r := by
 cases r <;> rfl

theorem geometry_result (queries : Array U32 22#usize) (start finish : Usize) :
 Port3_QueryInstall.result
   (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
    NFN_NEW_GeometryRawInterface.answer
    (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) =
 Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted queries start finish := by
 have same := congrArg (@forget _) (NFN_NFB_GeometryComposed.result_state_effects
   (State:=Unit) (Event:=Unit) queries start finish ())
 simpa only [forget_run] using same

#print axioms source
#print axioms slots
#print axioms pending_reply
#print axioms forget_run
#print axioms geometry_result
end NHV_NativeOps
