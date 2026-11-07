import PV_THR2_Spawn361MetadataChild70Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketChild70Store
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact returned continuation at the actual child site, on its operand store.
The only branch hypothesis is the named child's arbitrary returned case. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (argument : Data) (w : OWNER) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,26,[]⟩ = some argument)
    (returned : PV_THR2_OwnInitExactReturnedCases.ReturnedAt
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) H
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 70,loops := loops},parents,s⟩,w,es⟩,stack⟩
      (PV_THR2_F361.live.body.drop 70) PV_THR2_Source361PacketChildren.fn70 [.move (.local 26)]) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let t := write s ⟨a,26,[]⟩ none
    let r := H (.child PV_THR2_Source361PacketChildren.fn70 t.nextActivation [argument]) w
    ∃ value, r.answer = .returned (.ok value) ∧
      PV_THR2_Source361Full70.after B H
        ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 70,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
        ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 71,loops := loops},parents,
          PV_THR2_StaticReply.returnedStore t a [argument] 25 value⟩,r.world,es ++ r.events⟩,stack⟩ := by
  intro B t r
  have selected : operands B w a
      [.move (.local 26)] s = some ([argument],t) := by
    simp [operands,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      cell,t,write]
  have ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 70)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 70,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨value,ret⟩ := returned _ rfl ready [argument] t selected
  refine ⟨value,ret,?_⟩
  simp only [PV_THR2_Source361Full70.after,PV_THR2_IntrinsicAtContinuation.after,if_pos ready,
    PV_THR2_Source361Full70.finish]
  exact PV_THR2_ChildCallReturned.after B H s a parents loops _ _ _ _ _ w es stack [argument] t value selected ret
#print axioms after
end PV_THR2_PacketChild70Store
