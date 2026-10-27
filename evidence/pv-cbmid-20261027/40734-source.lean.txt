import R1Z.PV_CBM_CellsMaterializer
import R1Z.PV_CBM_MasksSelection
namespace R1Z.PV_CBM_CellsSelection
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_CBM_MasksSelection.Types

/-- Select the extracted state-producing reference and the explicit fresh-vector
wrapper. Native shipped/reference equality is still open. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {PV_CBM_MasksSelection.selected base ops with
    op132 := PV_CBM_CellsMaterializer.callback}

theorem op132_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op132 (Types base) (selected base ops) =
      PV_CBM_CellsMaterializer.callback := rfl

theorem op134_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op134 (Types base) (selected base ops) =
      PV_CBM_ReferenceRaw.reference.masks := rfl

#print axioms op132_reference
#print axioms op134_reference
end
end R1Z.PV_CBM_CellsSelection
