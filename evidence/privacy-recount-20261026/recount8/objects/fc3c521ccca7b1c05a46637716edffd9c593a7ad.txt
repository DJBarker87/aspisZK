import R1Z.PV_Join_Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_FieldDictionary
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BodyStore.selected ops with
    op100 := @ExternalFuns.op100 _ (PV_CB_Field.selected ops),
    op101 := @ExternalFuns.op101 _ (PV_CB_Field.selected ops),
    op105 := @ExternalFuns.op105 _ (PV_CB_Field.selected ops),
    op107 := @ExternalFuns.op107 _ (PV_CB_Field.selected ops),
    op109 := @ExternalFuns.op109 _ (PV_CB_Field.selected ops)}
theorem dictionary (ops : ExternalFuns) : selected ops = ProverRwP6BodyStore.selected ops := by
  have h100 : @ExternalFuns.op100 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op100 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op100Source.op100_source ops x).trans (PV_Join_Field.op100_source ops x).symm
  have h101 : @ExternalFuns.op101 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op101 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op101Source.op101_source ops x).trans (PV_Join_Field.op101_source ops x).symm
  have h105 : @ExternalFuns.op105 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op105 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op105Source.op105_source ops x).trans (PV_Join_Field.op105_source ops x).symm
  have h107 : @ExternalFuns.op107 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op107 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op107Source.op107_source ops x).trans (PV_Join_Field.op107_source ops x).symm
  have h109 : @ExternalFuns.op109 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op109 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op109Source.op109_source ops x).trans (PV_Join_Field.op109_source ops x).symm
  unfold selected
  rw [h100, h101, h105, h107, h109]
  rfl
#print axioms dictionary
end R1Z.PV_Join_FieldDictionary
