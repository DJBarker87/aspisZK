import R1Z.PV_CB3_Op258Ref
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Staged
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Prospective selection only: the full native P6 correspondence is open. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op258 := PV_CB3_Op258Ref.reference.all_slots_clear}

theorem op258_reference (ops : ExternalFuns)
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (selected ops).op258 values masks chi =
      PV_CB3_Op258Ref.reference.all_slots_clear values masks chi := rfl
#print axioms op258_reference
end R1Z.PV_CB3_Op258Staged
