import PV_THR2_Spawn361PacketStorage55Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketChild58Reached
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal reference cell and freshness, and the named child12801 returned case.
Consume the arbitrary reply, retaining its exact world and events. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (packet : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 58) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (referenceCell : c.store.cells ⟨c.frame.activation,18,[]⟩ = some packet)
    (returned : PV_THR2_OwnInitExactReturnedCases.ReturnedAt
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) H q
      (PV_THR2_F361.live.body.drop 58) PV_THR2_Source361PacketChildren.fn58
      [.move (.local 18)]) :
    ∃ d, (PV_THR2_Source361Full58.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) H q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 59) d ∧
      (∀ i, i ≠ 17 → i ≠ 18 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ value, d.store.cells ⟨d.frame.activation,17,[]⟩ = some value := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let t := write c.store ⟨c.frame.activation,18,[]⟩ none
  have selected : operands B q.current.world c.frame.activation
      [.move (.local 18)] c.store = some ([packet],t) := by
    simp [operands,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      referenceCell,t,write]
  obtain ⟨value,ret⟩ := returned c running ready [packet] t selected
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 58)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 58),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  change ∃ d, (PV_THR2_Source361Full58.after B H _).current.status = _ ∧ _
  simp only [PV_THR2_Source361Full58.after,PV_THR2_IntrinsicAtContinuation.after,
    if_pos isReady,PV_THR2_Source361Full58.finish]
  change ∃ d, (PV_THR2_IntrinsicChildCall.after B H s a parents loops
      (PV_THR2_F361.live.body.drop 59) PV_THR2_Source361Full58.source.1
      PV_THR2_Source361PacketChildren.fn58 [.move (.local 18)] 17 w es stack).current.status = .running d ∧ _
  rw [PV_THR2_ChildCallReturned.after B H s a parents loops _ _ _ _ _ w es stack
    [packet] t value selected ret]
  have ne : a ≠ t.nextActivation := by simpa [t,write] using Nat.ne_of_lt fresh
  have reverse : t.nextActivation ≠ a := Ne.symm ne
  have ne0 : a ≠ s.nextActivation := Nat.ne_of_lt fresh
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,value,?_⟩
  · simpa [PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,t] using Nat.lt_succ_of_lt fresh
  · intro i n17 n18
    simp [PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,
      write,ne0,ne,reverse,n17,n18,t]
  · simp [PV_THR2_StaticReply.returnedStore,write]
#print axioms after
end PV_THR2_Spawn361PacketChild58Reached
