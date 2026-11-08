import PV_THR2_Spawn361MetadataReference77Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketMetadata77Store
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact continuation on the complete supplied store; no dead cells discarded.
The captured cell at64 is an internal composition input. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List E) (stack : List Config)
 :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_THR2_Source361Chain77To81.after B
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 77,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 81,loops := loops},parents,
        PV_THR2_Spawn361MetadataReference77Reached.prepared s a⟩,w,es⟩,stack⟩ := by
  intro B
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 77)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 77,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 81)
      w PV_THR2_Source361Chain77To81.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 81),loops := loops},parents,PV_THR2_Spawn361MetadataReference77Reached.prepared s a⟩ := by
    have metadata : B.constant (.object [("kind",.object [("Adt",.array [.null,.array []])]),
        ("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    have completedReference : (PV_THR2_AggregateCompletion.carrier B).reference = B.reference := rfl
    simp [PV_THR2_Source361Chain77To81.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node89,PV_THR2_F361.node90,PV_THR2_F361.node91,PV_THR2_F361.node92,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,PV_THR2_Spawn361MetadataReference77Reached.prepared,metadata,reference,completedConstant,completedReference]
  simp only [PV_THR2_Source361Chain77To81.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain77To81.finish]
  rw [result]
/-- Foreign backing survives every explicit source write. -/
theorem frame (s : Store Data) (a : Nat) (p : Address) (other : p.activation ≠ a) :
    (PV_THR2_Spawn361MetadataReference77Reached.prepared s a).cells p = s.cells p := by
  simp only [PV_THR2_Spawn361MetadataReference77Reached.prepared,write,
    show ∀ i, p ≠ (⟨a,i,[]⟩ : Address) from fun i h => other (congrArg Address.activation h),if_false]
#print axioms after
#print axioms frame
end PV_THR2_PacketMetadata77Store
