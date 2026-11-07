import PV_THR2_Spawn361PacketPrefixReached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketEmptyReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Actual emitted12523 kind, retaining all generic metadata. -/
def kind : Data := PV_THR2_Source361Aggregate49.source.2.2.1
/-- Internal actual12523 control only; the empty aggregate is always constructed.
The selected source cells are preserved, with the exact new local21 value. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 49) c)
    (fresh : c.frame.activation < c.store.nextActivation) :
    ∃ d, (PV_THR2_Source361Aggregate49.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 50) d ∧
      (∀ i, i ≠ 21 → d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ value, d.store.cells ⟨d.frame.activation,21,[]⟩ = some value := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have completed : (PV_THR2_AggregateCompletion.carrier B).aggregate kind [] =
      (B.aggregate kind []).orElse (fun _ => some (PV_THR2_KeyValues.pack kind [])) := rfl
  have selected : ∃ value,
      (PV_STX2_Store.bind B s w a (.local 21) (.aggregate kind [])).orElse
        (fun _ => PV_STX2_Store.bind (PV_THR2_AggregateCompletion.carrier B) s w a (.local 21) (.aggregate kind [])) =
      some (write s ⟨a,21,[]⟩ (some value)) := by
    cases h : B.aggregate kind [] with
    | none => exact ⟨PV_THR2_KeyValues.pack kind [], by simp [PV_STX2_Store.bind,evaluate,operands,locate,writeAddress,h,completed]⟩
    | some v => exact ⟨v, by simp [PV_STX2_Store.bind,evaluate,operands,locate,writeAddress,h]⟩
  obtain ⟨value,selected⟩ := selected
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 49)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 49,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  change ∃ d, (PV_THR2_Source361Aggregate49.after B _).current.status = _ ∧ _
  simp only [PV_THR2_Source361Aggregate49.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Aggregate49.finish]
  change ∃ d, (PV_THR2_IntrinsicFrameAggregate.after B s a parents loops _ _ (.local 21) kind [] w es stack).current.status = _ ∧ _
  simp only [PV_THR2_IntrinsicFrameAggregate.after,selected,Option.orElse_some]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i ne; simp [write,ne]
  · exact ⟨value,by simp [write]⟩
#print axioms after
end PV_THR2_Spawn361PacketEmptyReached
