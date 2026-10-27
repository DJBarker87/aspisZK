import R1Z.PV_CBL_PathTypes
import R1Z.PV_CBL_PathBytesReference
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_PathBorrowSource
open ProverRwFull
set_option autoImplicit false

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base)) :
    @ExternalFuns (PV_CBL_PathTypes.selectedTypes base) :=
  letI : ExternalTypes := PV_CBL_PathTypes.selectedTypes base
  { ops with op25 := PV_CBL_PathBytesReference.path_bytes_reference,
             op29 := PV_CBL_PathBytesReference.path_bytes_reference }

theorem op25_source (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base))
    (p : alloc.vec.Vec U8) :
    @ExternalFuns.op25 (PV_CBL_PathTypes.selectedTypes base) (selected base ops) p =
      PV_CBL_PathBytesReference.path_bytes_reference p := rfl

theorem op29_source (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base))
    (p : alloc.vec.Vec U8) :
    @ExternalFuns.op29 (PV_CBL_PathTypes.selectedTypes base) (selected base ops) p =
      PV_CBL_PathBytesReference.path_bytes_reference p := rfl

#print axioms op25_source
#print axioms op29_source
end R1Z.PV_CBL_PathBorrowSource
