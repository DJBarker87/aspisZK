import PV_THR2_OwnInitExactReturnedCases
set_option autoImplicit false
namespace PV_THR2_Spawn361Names28Result
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Actual12200–12205 store, leaving every entry argument symbolic. -/
def prepared (s : Store Data) (a : Nat) (threadName identifier : Data) : Store Data :=
  write (write (write (write (write (write (write s ⟨a,10,[]⟩ none)
    ⟨a,11,[]⟩ none) ⟨a,11,[]⟩ (some identifier)) ⟨a,12,[]⟩ none)
    ⟨a,68,[]⟩ (some (.boolean false))) ⟨a,1,[]⟩ none) ⟨a,12,[]⟩ (some threadName)
/-- Internal input: stack-size cell derived at the actual361 entry.
Conditional on acceptance of the amended translator; no payload restriction. -/
theorem result (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (w : OWNER) (threadName identifier : Data)
    (nameCell : s.cells ⟨a,1,[]⟩ = some threadName)
    (idCell : s.cells ⟨a,9,[]⟩ = some identifier) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 34)
      w PV_THR2_Source361Chain28To34.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 34,loops := loops},
        parents,prepared s a threadName identifier⟩ := by
  intro B
  have flag (v : Bool) : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean v)])]),
      ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean v) := rfl
  have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
  simp [PV_THR2_Source361Chain28To34.chain,PV_THR2_Source15CaptureChain.prepend,
    PV_THR2_F361.node28,PV_THR2_F361.node29,PV_THR2_F361.node30,PV_THR2_F361.node31,PV_THR2_F361.node32,PV_THR2_F361.node33,
    PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
    nameCell,idCell,flag,completedConstant,write,prepared]
#print axioms result
end PV_THR2_Spawn361Names28Result
