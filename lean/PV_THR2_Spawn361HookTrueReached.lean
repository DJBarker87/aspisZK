import PV_THR2_Spawn361HookBranchReached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HookTrueReached
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal hook-true control and freshness, and named child12399 returned case.
Consume the arbitrary reply, retaining its exact world and events. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) 
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (returned : PV_THR2_OwnInitExactReturnedCases.ReturnedAt
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) H q
      (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41) PV_THR2_Source361HookChildren.fnTrueFull
      []) :
    ∃ d, (PV_THR2_Source361HookTrueFull.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) H q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41) d ∧
      (∀ i, i ≠ 13 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ value, d.store.cells ⟨d.frame.activation,13,[]⟩ = some value := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let t := c.store
  have selected : operands B q.current.world c.frame.activation [] c.store = some ([],t) := rfl
  obtain ⟨value,ret⟩ := returned c running ready [] t selected
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41)
      ⟨{activation := a,remaining := (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  change ∃ d, (PV_THR2_Source361HookTrueFull.after B H _).current.status = _ ∧ _
  simp only [PV_THR2_Source361HookTrueFull.after,PV_THR2_IntrinsicAtContinuation.after,
    if_pos isReady,PV_THR2_Source361HookTrueFull.finish]
  change ∃ d, (PV_THR2_IntrinsicChildCall.after B H s a parents loops
      (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41) PV_THR2_Source361HookTrueFull.source.1
      PV_THR2_Source361HookChildren.fnTrueFull [] 13 w es stack).current.status = .running d ∧ _
  rw [PV_THR2_ChildCallReturned.after B H s a parents loops _ _ _ _ _ w es stack
    [] t value selected ret]
  have ne : a ≠ t.nextActivation := by simpa [t,write] using Nat.ne_of_lt fresh
  have reverse : t.nextActivation ≠ a := Ne.symm ne
  have ne0 : a ≠ s.nextActivation := Nat.ne_of_lt fresh
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,value,?_⟩
  · simpa [PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,t] using Nat.lt_succ_of_lt fresh
  · intro i n13
    simp [PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
      write,ne0,ne,reverse,n13,t]
  · simp [PV_THR2_StaticReply.returnedStore,write]
#print axioms after
end PV_THR2_Spawn361HookTrueReached
