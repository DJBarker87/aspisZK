import PV_THR2_Spawn361PacketField82Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketField82Store
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact two-statement13324/13325 suffix on its actual input Store. This exposes
all backing cells, beyond the existing local-only frame conclusion. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (p : Address) (w : OWNER) (es : List E) (stack : List Config)
    (referenceCell : s.cells ⟨a,29,[]⟩ = some (PV_STX2_TypedReferences.reference p .null)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_THR2_Source361Chain82To84.after B
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 82,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 84,loops := loops},parents,
        PV_THR2_Spawn361PacketField82Reached.prepared s a p⟩,w,es⟩,stack⟩ := by
  intro B
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 82)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 82,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 84)
      w PV_THR2_Source361Chain82To84.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 84),loops := loops},parents,PV_THR2_Spawn361PacketField82Reached.prepared s a p⟩ := by
    have metadata : B.constant (.object [("kind",.object [("Adt",.array [.null,.array []])]),
        ("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
    have dereference (address : Address) : B.dereference w (PV_STX2_TypedReferences.reference address .null) = some address :=
      PV_STX2_TypedReferences.dereference _ _ _ _
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    have completedReference : (PV_THR2_AggregateCompletion.carrier B).reference = B.reference := rfl
    simp [PV_THR2_Source361Chain82To84.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node94,PV_THR2_F361.node95,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,PV_THR2_Spawn361PacketField82Reached.prepared,metadata,reference,completedConstant,completedReference,referenceCell,dereference]
  simp only [PV_THR2_Source361Chain82To84.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain82To84.finish]
  rw [result]
#print axioms after
end PV_THR2_PacketField82Store
