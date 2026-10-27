import R1Z.PV_CBM_RowsReference
import R1Z.PV_CBM_CellsSelection
namespace R1Z.PV_CBM_RowsSelection
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_CBM_CellsSelection.Types

def callback : Result (core.result.Result (alloc.vec.Vec U16) PV_CBM_CellsMaterializer.LayoutError) :=
  PV_CBM_CellsMaterializer.snapshot (PV_CBM_RowsRaw.reference.fill_rows (alloc.vec.Vec.new U16))

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {PV_CBM_CellsSelection.selected base ops with op133 := callback}

/-- Reference-only: no native shipped/reference equality is asserted. -/
theorem op133_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op133 (Types base) (selected base ops) = callback := rfl
#print axioms op133_reference
end
end R1Z.PV_CBM_RowsSelection
