import NMX_R3_DecoderFold
import NMX_R2_LaneView
set_option autoImplicit false
noncomputable section
namespace NMX_R3_LaneInstance
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets

def payload (a : NCV_Reference.Lane) : Lane :=
 ⟨a.bump,a.master,a.lane_id,⟨a.next_leaf_index,a.root,a.frontier⟩⟩

theorem payload_exact (a : NCV_Reference.Lane) :
 NMX_R2_Carrier.lane (payload a) = NMX_R3_LaneCarrier.lane a := rfl

def native (owner : Nat) (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) : NMX_R2_RawChildren.LaneNative :=
 fun b env => match NCV_Reference.decode_lane_ref b with
 | .ok (.Err ()) => ⟨.ret (.error .invalidAccountData),[]⟩
 | .ok (.Ok a) => if allocationSucceeded (NMX_R2_Carrier.bytes b) env
   then ⟨.ret (.ok ⟨owner,payload a⟩),[]⟩ else ⟨.abort,[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

/-- The raw Box payload is the emitted reference value, not a selected
successful reply. LaneTotal supplies every Result and every slice length. -/
theorem observation (owner : Nat) (allocationSucceeded : RSL.Bytes → RSL.Env → Bool)
 (b : Slice U8) (env : RSL.Env) :
 NMX_R2_RawChildren.mapObs (fun box => NMX_R2_Carrier.lane box.payload)
  (native owner allocationSucceeded b env) =
 NMX_R3_DecoderFold.decode allocationSucceeded (NMX_R2_Carrier.bytes b) env := by
 obtain ⟨r,call,mapped⟩ := NMX_R3_LaneTotal.value b
 have hs : NMX_R3_DecoderFold.source (NMX_R2_Carrier.bytes b) = NMX_R3_LaneCarrier.result r :=
  (NMX_R3_DecoderFold.source_eq_reference _).trans ((NMX_R3_LanePort.pure_eq _).trans mapped.symm)
 unfold native NMX_R3_DecoderFold.decode
 rw [call,hs]
 cases r with
 | Err u => cases u; rfl
 | Ok a =>
  cases flag : allocationSucceeded (NMX_R2_Carrier.bytes b) env <;>
   simp only [NMX_R3_LaneCarrier.result,flag,Bool.false_eq_true,↓reduceIte,
    NMX_R2_RawChildren.mapObs,payload_exact]

theorem raw (owner : Nat) (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) :
 NMX_R2_RawChildren.RowSpec_217 (native owner allocationSucceeded) := by
 intro b env
 rw [observation]
 exact NMX_R3_DecoderFold.root allocationSucceeded _ env trivial

theorem packet (owner : Nat) (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) :
 RSL.TX2_217.RowSpec_217 (NMX_R2_LaneView.view (native owner allocationSucceeded)) :=
 NMX_R2_LaneView.canonical _ (raw owner allocationSucceeded)
#print axioms payload_exact
#print axioms observation
#print axioms raw
#print axioms packet
end NMX_R3_LaneInstance
end
