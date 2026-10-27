import R1Z.PV_CBL_LibraryShapeTypes
import R1Z.PV_CBL_PathTypes
import R1Z.PV_CBL_ShaTypes
namespace R1Z.PV_CBL_LibraryShapeFrame
open ProverRwFull
set_option autoImplicit false

theorem idempotent (base : ExternalTypes) :
    PV_CBL_LibraryShapeTypes.selectedTypes (PV_CBL_LibraryShapeTypes.selectedTypes base) =
      PV_CBL_LibraryShapeTypes.selectedTypes base := rfl

theorem path_commutes (base : ExternalTypes) :
    PV_CBL_LibraryShapeTypes.selectedTypes (PV_CBL_PathTypes.selectedTypes base) =
      PV_CBL_PathTypes.selectedTypes (PV_CBL_LibraryShapeTypes.selectedTypes base) := rfl

theorem sha_commutes (base : ExternalTypes) :
    PV_CBL_LibraryShapeTypes.selectedTypes (PV_CBL_ShaTypes.selectedTypes base) =
      PV_CBL_ShaTypes.selectedTypes (PV_CBL_LibraryShapeTypes.selectedTypes base) := rfl

#print axioms idempotent
#print axioms path_commutes
#print axioms sha_commutes
end R1Z.PV_CBL_LibraryShapeFrame
