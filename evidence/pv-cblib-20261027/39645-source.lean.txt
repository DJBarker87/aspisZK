import R1Z.PV_CBL_Op208Outcomes
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_Op208Shape
open ProverRwFull
set_option autoImplicit false

/-- This is an explicit decomposition only: compress256 still has to be bound
without a stub before V232 is credited as discharged. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_ShaTypes.selectedTypes base))
    (compress : PV_CBL_Op208Extracted.Compression base) :
    @ExternalFuns (PV_CBL_ShaTypes.selectedTypes base) :=
  letI : ExternalTypes := PV_CBL_ShaTypes.selectedTypes base
  { ops with op208 := PV_CBL_Op208Extracted.update_blocks base compress }

theorem extracted_shape (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_ShaTypes.selectedTypes base))
    (compress : PV_CBL_Op208Extracted.Compression base)
    (self : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) :
    @ExternalFuns.op208 (PV_CBL_ShaTypes.selectedTypes base)
      (selected base ops compress) self blocks =
        PV_CBL_Op208Extracted.update_blocks base compress self blocks := rfl
#print axioms extracted_shape
end R1Z.PV_CBL_Op208Shape
