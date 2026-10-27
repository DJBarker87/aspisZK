import R1Z.PV_CBL_PathTypes
import R1Z.PV_CBL_PathOwnedReference
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_PathBorrowSource
open ProverRwFull
set_option autoImplicit false

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base)) :
    @ExternalFuns (PV_CBL_PathTypes.selectedTypes base) :=
  letI : ExternalTypes := PV_CBL_PathTypes.selectedTypes base
  { ops with op25 := PV_CBL_PathOwnedReference.path_owned_reference base,
             op29 := PV_CBL_PathOwnedReference.path_owned_reference base }

theorem op25_source (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base))
    (p : @std.path.PathBuf base) :
    @ExternalFuns.op25 (PV_CBL_PathTypes.selectedTypes base) (selected base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p := rfl

theorem op29_source (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_PathTypes.selectedTypes base))
    (p : @std.path.PathBuf base) :
    @ExternalFuns.op29 (PV_CBL_PathTypes.selectedTypes base) (selected base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p := rfl

#print axioms op25_source
#print axioms op29_source
end R1Z.PV_CBL_PathBorrowSource
