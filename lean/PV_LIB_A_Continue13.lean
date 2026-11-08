import PV_LIB_A_PrefixMachine11
import PV_THR2_IntrinsicCompatible
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Continue13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Symbolic continue rule: the loop body stays abstract, so the kernel never
normalizes the enormous emitted body merely to check a backedge. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (site : PV_STX2_Syntax.Site)
    (body rest afterLoop : List PV_STX2_SliceSyntax.Node) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running ⟨{activation := a,remaining := .continueLoop site 0 :: rest,loops := ⟨body,afterLoop⟩ :: loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running ⟨{activation := a,remaining := body,loops := ⟨body,afterLoop⟩ :: loops},parents,s⟩,w,es⟩,stack⟩,none⟩ := by
  have quiet : Quiet P ⟨⟨.running ⟨{activation := a,remaining := .continueLoop site 0 :: rest,loops := ⟨body,afterLoop⟩ :: loops},parents,s⟩,w,es⟩,stack⟩ := by
    constructor
    · intro c hc; cases hc; rfl
    · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩
  rw [PV_LIB_A_PrefixMachine11.step C K P resources encode H values _ quiet]
  apply congrArg (fun q => (⟨q,none⟩ : SourceState))
  rw [PV_THR2_IntrinsicCompatible.step _ _ _ _ _ _ _ _ (by rfl)]
  simp [PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step]

#print axioms run
end PV_LIB_A_Continue13
