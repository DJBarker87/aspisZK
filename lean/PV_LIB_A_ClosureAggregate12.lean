import PV_LIB_A_Continuation12
import PV_THR2_Source15ClosureAggregate
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ClosureAggregate12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K P H (PV_THR2_Source15ClosureAggregate.steps q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rw [PV_THR2_IntrinsicAtContinuation.frame c h]
  refine ⟨?_,True.intro⟩
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Source3472 on the corrected machine: exact closure metadata and captured
locals, with every aggregate-read failure retained. All other frontiers stop. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (PV_THR2_Source15ClosureAggregate.steps q) ⟨q,none⟩ =
      ⟨PV_THR2_Source15ClosureAggregate.after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _ (trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState))
    (PV_THR2_Source15ClosureAggregate.run C K P H q)

#print axioms trace
#print axioms run
end PV_LIB_A_ClosureAggregate12
