import NKY_BoxCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxComplete
open Aeneas Aeneas.Std Result
open NKY_BoxAction
/-- Full actual-carrier TX2:216 implication. Cut fields are the reviewed
parent windows/pointer observation; the CLOSED raw child is instantiated at
these SAME bytes. Allocation outcome is arbitrary and actually consumed. -/
theorem checkpoint {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (heap : NKY_BoxFrame.Heap NJQ_Carrier.CC)
 (reservation : NP6_StdModel.Reservation) (allocated : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result (Owned NJQ_Carrier.CC) PE)
 (cut : NKY_BoxCarrier.CheckpointCut bytes raw out allocated) :
 NKY_BoxCarrier.native allocator before 176 reservation out=
 run allocator before 176 reservation allocated (NKF_CheckpointBox.reference bytes) ∧
 NKY_BoxPacket.Law allocator before 176 8 reservation allocated heap
  (NKF_CheckpointBox.reference bytes) := by
 have value : ok (NKY_BoxCarrier.erase out)=NKF_CheckpointBox.reference bytes :=
  NKP_BoxCuts.checkpoint reservation bytes raw (NKY_BoxCarrier.erase out) ⟨cut.decoder,cut.fields⟩
 exact ⟨(NKY_BoxCarrier.association allocator before 176 reservation allocated out cut.owner).trans
  (congrArg (run allocator before 176 reservation allocated) value),NKY_BoxPacket.complete _ _ _ _ _ _ _ _⟩

/-- Full actual-carrier TX2:218 implication, retaining the identical master
allocation action, every failure/divergence arm, post, cleanup-free return and
frame. Neither a fresh independent Box nor a success premise is substituted. -/
theorem master {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (heap : NKY_BoxFrame.Heap NJQ_Carrier.CM)
 (reservation : NP6_StdModel.Reservation) (allocated : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result (Owned NJQ_Carrier.CM) PE)
 (cut : NKY_BoxCarrier.MasterCut bytes raw out allocated) :
 NKY_BoxCarrier.native allocator before 304 reservation out=
 run allocator before 304 reservation allocated (NKF_MasterBox.reference bytes) ∧
 NKY_BoxPacket.Law allocator before 304 8 reservation allocated heap
  (NKF_MasterBox.reference bytes) := by
 have value : ok (NKY_BoxCarrier.erase out)=NKF_MasterBox.reference bytes :=
  NKP_BoxCuts.master reservation bytes raw (NKY_BoxCarrier.erase out) ⟨cut.decoder,cut.fields⟩
 exact ⟨(NKY_BoxCarrier.association allocator before 304 reservation allocated out cut.owner).trans
  (congrArg (run allocator before 304 reservation allocated) value),NKY_BoxPacket.complete _ _ _ _ _ _ _ _⟩
#print checkpoint
#print axioms checkpoint
#print master
#print axioms master
end AspisR1.NKY_BoxComplete
end
