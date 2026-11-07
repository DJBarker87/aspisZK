import PV_THR2_Spawn361PacketEmpty53Reached
import PV_THR2_AggregateLocalValue
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketAggregate54Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal actual12672 inputs, all derived at the original drop54.
Construct the packet without fixing the base aggregate value. Preserve every
other local and the fresh activation bound. Amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (scope packet empty : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 54) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (scopeCell : c.store.cells ⟨c.frame.activation,19,[]⟩ = some scope)
    (packetCell : c.store.cells ⟨c.frame.activation,20,[]⟩ = some packet)
    (emptyCell : c.store.cells ⟨c.frame.activation,22,[]⟩ = some empty) :
    ∃ d, (PV_THR2_Source361Aggregate54.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 55) d ∧
      (∀ i, i ≠ 18 → i ≠ 19 → i ≠ 20 → i ≠ 22 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ value, d.store.cells ⟨d.frame.activation,18,[]⟩ = some value := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let t := write (write (write c.store ⟨c.frame.activation,19,[]⟩ none)
    ⟨c.frame.activation,20,[]⟩ none) ⟨c.frame.activation,22,[]⟩ none
  have selected : PV_STX2_Store.operands B q.current.world c.frame.activation
      (PV_THR2_AggregateLocalValue.captures [19,20,22]) c.store = some ([scope,packet,empty],t) := by
    simp [PV_THR2_AggregateLocalValue.captures,PV_STX2_Store.operands,operand,
      PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,scopeCell,packetCell,emptyCell,t,write]
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let kind := PV_THR2_Source361Aggregate54.source.2.2.1
  have completed : (PV_THR2_AggregateCompletion.carrier B).aggregate kind [scope,packet,empty] =
      (B.aggregate kind [scope,packet,empty]).orElse
        (fun _ => some (PV_THR2_KeyValues.pack kind [scope,packet,empty])) := rfl
  obtain ⟨value,result⟩ := PV_THR2_AggregateLocalValue.after B s a parents loops
    (PV_THR2_F361.live.body.drop 55) PV_THR2_Source361Aggregate54.source.1 18 kind [19,20,22]
    w es stack [scope,packet,empty] t selected completed
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 54)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 54,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  change ∃ d, (PV_THR2_Source361Aggregate54.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Aggregate54.after,PV_THR2_IntrinsicAtContinuation.after,
    if_pos isReady,PV_THR2_Source361Aggregate54.finish]
  change ∃ d, (PV_THR2_IntrinsicFrameAggregate.after B s a parents loops
    (PV_THR2_F361.live.body.drop 55) PV_THR2_Source361Aggregate54.source.1 (.local 18) kind
    (PV_THR2_AggregateLocalValue.captures [19,20,22]) w es stack).current.status = .running d ∧ _
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,value,?_⟩
  · exact fresh
  · intro i n18 n19 n20 n22; simp [t,write,n18,n19,n20,n22]
  · simp [write]
#print axioms after
end PV_THR2_Spawn361PacketAggregate54Reached
