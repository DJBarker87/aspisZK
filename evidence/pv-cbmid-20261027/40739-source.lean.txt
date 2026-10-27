import R1Z.PV_CBM_CellsSelection
namespace R1Z.PV_CBM_CallbackBundle
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_CBM_CellsSelection.Types
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) := PV_CBM_CellsSelection.selected base ops

/-- Reference-only equation. No shipped source law is claimed before the P6 gate. -/
theorem op134_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op134 (Types base) (selected base ops) =
      PV_CBM_ReferenceRaw.reference.masks := rfl
/-- Complete Result reference equation; native association remains open. -/
theorem op132_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op132 (Types base) (selected base ops) =
      PV_CBM_CellsMaterializer.callback := rfl
#print axioms op132_reference
#print axioms op134_reference
end
end R1Z.PV_CBM_CallbackBundle
