import PV_LIB_A_PrefixMachine11
import PV_THR2_TableIntrinsic
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceSelectCongruence14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
abbrev Agree := @PV_THR2_TableIntrinsic.Agree

theorem select (P Q : Data → Option PV_STX2_SliceSyntax.Program) (c : Config)
    (same : PV_THR2_TableStepShape.Agree P Q c) : sourceSelect P c = sourceSelect Q c := by
  unfold sourceSelect
  cases done : c.frame.completed with
  | some r => rfl
  | none =>
    cases waiting : c.frame.waiting with
    | none => rfl
    | some wait =>
      dsimp only
      cases request : wait.request with
      | child fn a args => simp [request,same wait fn a args done waiting request]
      | copy x y z => simp [request]
      | drop fn x => simp [request]

#print axioms select
end PV_LIB_A_SourceSelectCongruence14
