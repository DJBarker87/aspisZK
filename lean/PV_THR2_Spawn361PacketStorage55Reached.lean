import PV_THR2_Spawn361PacketAggregate54Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketStorage55Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source12673–12675 ends the packet input locals. -/
def prepared (s : Store Data) (a : Nat) := write (write (write s ⟨a,22,[]⟩ none) ⟨a,20,[]⟩ none) ⟨a,19,[]⟩ none
/-- Internal aggregate12672 output control and freshness. Compose the retained suffix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 55) c)
    (fresh : c.frame.activation < c.store.nextActivation)
 :
    ∃ d, (PV_THR2_Source361Chain55To58.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 58) d ∧
      (∀ i, i ≠ 19 → i ≠ 20 → i ≠ 22 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 55)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 55),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 58)
      w PV_THR2_Source361Chain55To58.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 58,loops := loops},parents,prepared s a⟩ := by
    simp [PV_THR2_Source361Chain55To58.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node67,PV_THR2_F361.node68,PV_THR2_F361.node69,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared]
  change ∃ d, (PV_THR2_Source361Chain55To58.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain55To58.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain55To58.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_⟩
  · exact fresh
  · intro i n19 n20 n22; simp [prepared,write,n19,n20,n22]
#print axioms after
end PV_THR2_Spawn361PacketStorage55Reached
