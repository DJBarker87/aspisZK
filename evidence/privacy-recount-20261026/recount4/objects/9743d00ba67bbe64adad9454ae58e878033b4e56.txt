import R1Z.PV_Join_Borrow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_BorrowDictionary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BodyStore.selected ops with
    op127 := @ExternalFuns.op127 _ (PV_CB_Borrow.selected ops),
    op128 := @ExternalFuns.op128 _ (PV_CB_Borrow.selected ops),
    op130 := @ExternalFuns.op130 _ (PV_CB_Borrow.selected ops),
    op131 := @ExternalFuns.op131 _ (PV_CB_Borrow.selected ops)}
theorem dictionary (ops : ExternalFuns) : selected ops = ProverRwP6BodyStore.selected ops := by
  have h127 : @ExternalFuns.op127 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op127 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op127Source.op127_source ops inst x).trans (PV_Join_Borrow.op127_source ops inst x).symm
  have h128 : @ExternalFuns.op128 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op128 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op128Source.op128_source ops inst x).trans (PV_Join_Borrow.op128_source ops inst x).symm
  have h130 : @ExternalFuns.op130 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op130 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op130Source.op130_source ops inst x).trans (PV_Join_Borrow.op130_source ops inst x).symm
  have h131 : @ExternalFuns.op131 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op131 _ (ProverRwP6BodyStore.selected ops) := by
    funext T Z view inst x
    exact (PV_CB_Op131Source.op131_source ops view inst x).trans (PV_Join_Borrow.op131_source ops view inst x).symm
  unfold selected
  rw [h127, h128, h130, h131]
  rfl
#print axioms dictionary
end R1Z.PV_Join_BorrowDictionary
