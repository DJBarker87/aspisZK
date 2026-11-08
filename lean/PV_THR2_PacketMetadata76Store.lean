import PV_THR2_Spawn361MetadataAggregate76Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketMetadata76Store
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact metadata aggregate store. Inputs are the three internal cells, never
endpoint hypotheses; arbitrary aggregate payloads and complete Store persist. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (metadata hook counter : Data) (w : OWNER) (es : List E) (stack : List Config)
    (metadataCell : s.cells ⟨a,25,[]⟩ = some metadata)
    (hookCell : s.cells ⟨a,13,[]⟩ = some hook)
    (counterCell : s.cells ⟨a,23,[]⟩ = some counter) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let t := write (write (write s ⟨a,25,[]⟩ none) ⟨a,13,[]⟩ none) ⟨a,23,[]⟩ none
    ∃ value, PV_THR2_Source361Aggregate76.after B
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 77,loops := loops},parents,
        write t ⟨a,27,[]⟩ (some value)⟩,w,es⟩,stack⟩ := by
  intro B t
  have selected : PV_STX2_Store.operands B w a
      (PV_THR2_AggregateLocalValue.captures [25,13,23]) s = some ([metadata,hook,counter],t) := by
    simp [PV_THR2_AggregateLocalValue.captures,PV_STX2_Store.operands,operand,
      PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,metadataCell,hookCell,counterCell,t,write]
  let kind := PV_THR2_Source361Aggregate76.source.2.2.1
  have completed : (PV_THR2_AggregateCompletion.carrier B).aggregate kind [metadata,hook,counter] =
      (B.aggregate kind [metadata,hook,counter]).orElse
        (fun _ => some (PV_THR2_KeyValues.pack kind [metadata,hook,counter])) := rfl
  obtain ⟨value,result⟩ := PV_THR2_AggregateLocalValue.after B s a parents loops
    (PV_THR2_F361.live.body.drop 77) PV_THR2_Source361Aggregate76.source.1 27 kind [25,13,23]
    w es stack [metadata,hook,counter] t selected completed
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 76)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  refine ⟨value,?_⟩
  simp only [PV_THR2_Source361Aggregate76.after,PV_THR2_IntrinsicAtContinuation.after,
    if_pos isReady,PV_THR2_Source361Aggregate76.finish]
  exact result
#print axioms after
end PV_THR2_PacketMetadata76Store
