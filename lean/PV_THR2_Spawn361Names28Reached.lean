import PV_THR2_Spawn361Names28Result
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361Names28Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal actual12200 control/cells and entry-derived freshness.
Compose source28–33 without inspecting any child payload representation. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (threadName identifier : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 28) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (nameCell : c.store.cells ⟨c.frame.activation,1,[]⟩ = some threadName)
    (idCell : c.store.cells ⟨c.frame.activation,9,[]⟩ = some identifier) :
    ∃ d, (PV_THR2_Source361Chain28To34.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 34) d ∧
      (∀ i, i ≠ 1 → i ≠ 10 → i ≠ 11 → i ≠ 12 → i ≠ 68 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,11,[]⟩ = some identifier ∧
      d.store.cells ⟨d.frame.activation,12,[]⟩ = some threadName := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 28)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 28,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  simp only [PV_THR2_Source361Chain28To34.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain28To34.finish]
  rw [PV_THR2_Spawn361Names28Result.result C b s a parents loops w threadName identifier nameCell idCell]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · exact fresh
  · intro i n1 n10 n11 n12 n68
    simp [PV_THR2_Spawn361Names28Result.prepared,write,n1,n10,n11,n12,n68]
  · simp [PV_THR2_Spawn361Names28Result.prepared,write]
  · simp [PV_THR2_Spawn361Names28Result.prepared,write]
#print axioms after
end PV_THR2_Spawn361Names28Reached
