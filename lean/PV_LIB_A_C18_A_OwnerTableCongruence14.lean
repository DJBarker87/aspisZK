import PV_LIB_A_C18_A_PrefixMachine11
import PV_THR2_TableIntrinsic
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OwnerTableCongruence14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
abbrev Agree := @PV_THR2_TableIntrinsic.Agree

theorem uniform (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (s : State)
    (same : Agree P Q s) :
    PV_THR2_OwnUniformBindings.step C K P H s = PV_THR2_OwnUniformBindings.step C K Q H s := by
  unfold PV_THR2_OwnUniformBindings.step
  rw [PV_THR2_TableIntrinsic.step C K P Q H s same]

theorem operator (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (s : State)
    (same : Agree P Q s) :
    PV_THR2_OperatorInterpreter.step C K P H s = PV_THR2_OperatorInterpreter.step C K Q H s := by
  unfold PV_THR2_OperatorInterpreter.step
  cases status : s.current.status with
  | running c =>
    simp only [status]
    cases ha : PV_THR2_OperatorAction.selected c with
    | none => exact uniform C K P Q H s same
    | some kind => cases kind <;> exact uniform _ K P Q _ s same
  | returned r store => exact uniform C K P Q H s same
  | fault f store => exact uniform C K P Q H s same
  | undefined site store => exact uniform C K P Q H s same

theorem owner (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (s : State) (same : Agree P Q s) :
    PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s =
      PV_THR2_OwnInitInterpreterBridged.step C K Q resources encode H s := by
  unfold PV_THR2_OwnInitInterpreterBridged.step
  cases status : s.current.status with
  | running c =>
    simp only [status]
    split <;> exact operator C K P Q _ s same
  | returned r store => exact operator C K P Q H s same
  | fault f store => exact operator C K P Q H s same
  | undefined site store => exact operator C K P Q H s same

#print axioms uniform
#print axioms operator
#print axioms owner
end PV_LIB_A_OwnerTableCongruence14
