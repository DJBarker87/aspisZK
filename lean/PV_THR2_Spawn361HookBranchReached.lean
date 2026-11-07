import PV_THR2_Spawn361HooksPrefixReached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HookBranchReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal derived control and Boolean representation of the Builder field.
Both hook arms are retained. Conditional on acceptance of the amended translator. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b flag : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 40) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (hooksCell : c.store.cells ⟨c.frame.activation,14,[]⟩ = some (.boolean flag)) :
    ∃ d, (PV_THR2_Source361HookBranch.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready
        ((if flag then PV_THR2_F361.block42 else PV_THR2_F361.block51) ++ PV_THR2_F361.live.body.drop 41) d ∧
      (∀ i, i ≠ 14 → d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change s.cells ⟨a,14,[]⟩ = some (.boolean flag) at hooksCell
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 40)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 40,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have truth : B.truth (.boolean flag) = some flag := rfl
  change ∃ d, (PV_THR2_Source361HookBranch.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361HookBranch.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361HookBranch.finish,PV_THR2_IntrinsicFrameBranch.result,hooksCell,truth]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_⟩
  · exact fresh
  · intro i ni; simp [write,ni]
#print axioms after
end PV_THR2_Spawn361HookBranchReached
