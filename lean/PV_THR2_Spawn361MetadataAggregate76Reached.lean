import PV_THR2_Spawn361MetadataStorage71Reached
import PV_THR2_AggregateLocalValue
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361MetadataAggregate76Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal actual13129 inputs, all derived at the original drop54.
Construct the metadata closure without fixing the base aggregate value. Preserve every
other local and the fresh activation bound. Amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (metadata hook counter : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 76) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (metadataCell : c.store.cells ⟨c.frame.activation,25,[]⟩ = some metadata)
    (hookCell : c.store.cells ⟨c.frame.activation,13,[]⟩ = some hook)
    (counterCell : c.store.cells ⟨c.frame.activation,23,[]⟩ = some counter) :
    ∃ d, (PV_THR2_Source361Aggregate76.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 77) d ∧
      (∀ i, i ≠ 27 → i ≠ 25 → i ≠ 13 → i ≠ 23 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ value, d.store.cells ⟨d.frame.activation,27,[]⟩ = some value := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let t := write (write (write c.store ⟨c.frame.activation,25,[]⟩ none)
    ⟨c.frame.activation,13,[]⟩ none) ⟨c.frame.activation,23,[]⟩ none
  have selected : PV_STX2_Store.operands B q.current.world c.frame.activation
      (PV_THR2_AggregateLocalValue.captures [25,13,23]) c.store = some ([metadata,hook,counter],t) := by
    simp [PV_THR2_AggregateLocalValue.captures,PV_STX2_Store.operands,operand,
      PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,metadataCell,hookCell,counterCell,t,write]
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let kind := PV_THR2_Source361Aggregate76.source.2.2.1
  have completed : (PV_THR2_AggregateCompletion.carrier B).aggregate kind [metadata,hook,counter] =
      (B.aggregate kind [metadata,hook,counter]).orElse
        (fun _ => some (PV_THR2_KeyValues.pack kind [metadata,hook,counter])) := rfl
  obtain ⟨value,result⟩ := PV_THR2_AggregateLocalValue.after B s a parents loops
    (PV_THR2_F361.live.body.drop 77) PV_THR2_Source361Aggregate76.source.1 27 kind [25,13,23]
    w es stack [metadata,hook,counter] t selected completed
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 76)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  change ∃ d, (PV_THR2_Source361Aggregate76.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Aggregate76.after,PV_THR2_IntrinsicAtContinuation.after,
    if_pos isReady,PV_THR2_Source361Aggregate76.finish]
  change ∃ d, (PV_THR2_IntrinsicFrameAggregate.after B s a parents loops
    (PV_THR2_F361.live.body.drop 77) PV_THR2_Source361Aggregate76.source.1 (.local 27) kind
    (PV_THR2_AggregateLocalValue.captures [25,13,23]) w es stack).current.status = .running d ∧ _
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,value,?_⟩
  · exact fresh
  · intro i n18 n19 n20 n22; simp [t,write,n18,n19,n20,n22]
  · simp [write]
#print axioms after
end PV_THR2_Spawn361MetadataAggregate76Reached
