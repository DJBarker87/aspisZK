import PV_THR2_Spawn361MetadataStorage71Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketMetadata71Store
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact continuation on the complete supplied store; no dead cells discarded.
The captured cell at64 is an internal composition input. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List E) (stack : List Config)
 :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_THR2_Source361Chain71To76.after B
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 71,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,
        PV_THR2_Spawn361MetadataStorage71Reached.prepared s a⟩,w,es⟩,stack⟩ := by
  intro B
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 71)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 71,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 76)
      w PV_THR2_Source361Chain71To76.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,PV_THR2_Spawn361MetadataStorage71Reached.prepared s a⟩ := by
    have literal (v : Bool) : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean v)])]),
        ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean v) := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    simp [PV_THR2_Source361Chain71To76.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node83,PV_THR2_F361.node84,PV_THR2_F361.node85,
      PV_THR2_F361.node86,PV_THR2_F361.node87,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,PV_THR2_Spawn361MetadataStorage71Reached.prepared,literal,completedConstant]
  simp only [PV_THR2_Source361Chain71To76.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain71To76.finish]
  rw [result]
/-- Foreign backing survives every explicit source write. -/
theorem frame (s : Store Data) (a : Nat) (p : Address) (other : p.activation ≠ a) :
    (PV_THR2_Spawn361MetadataStorage71Reached.prepared s a).cells p = s.cells p := by
  simp only [PV_THR2_Spawn361MetadataStorage71Reached.prepared,write,
    show ∀ i, p ≠ (⟨a,i,[]⟩ : Address) from fun i h => other (congrArg Address.activation h),if_false]
#print axioms after
#print axioms frame
end PV_THR2_PacketMetadata71Store
