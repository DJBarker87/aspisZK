import PV_THR2_Spawn361Names28Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HooksPrefixReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Actual12291–12295 stores; no_hooks remains an arbitrary typed payload. -/
def prepared (s : Store Data) (a : Nat) (no_hooks : Data) :=
  write (write (write (write (write s ⟨a,12,[]⟩ none) ⟨a,11,[]⟩ none)
    ⟨a,13,[]⟩ none) ⟨a,14,[]⟩ none) ⟨a,14,[]⟩ (some no_hooks)
/-- Internal actual123xx control and local3 cell derived by retained entry.
This reaches the hook match without selecting either arm or assuming a tag. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (no_hooks : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 35) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (hooksCell : c.store.cells ⟨c.frame.activation,3,[]⟩ = some no_hooks) :
    ∃ d, (PV_THR2_Source361Chain35To40.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 40) d ∧
      (∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 14 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,14,[]⟩ = some no_hooks := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change s.cells ⟨a,3,[]⟩ = some no_hooks at hooksCell
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 35)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 35,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 40)
      w PV_THR2_Source361Chain35To40.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 40,loops := loops},parents,prepared s a no_hooks⟩ := by
    have completedField : (PV_THR2_AggregateCompletion.carrier B).field = B.field := rfl
    simp [PV_THR2_Source361Chain35To40.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node35,PV_THR2_F361.node36,PV_THR2_F361.node37,PV_THR2_F361.node38,PV_THR2_F361.node39,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      hooksCell,write,prepared]
  change ∃ d, (PV_THR2_Source361Chain35To40.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain35To40.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain35To40.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n11 n12 n13 n14; simp [prepared,write,n11,n12,n13,n14]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361HooksPrefixReached
