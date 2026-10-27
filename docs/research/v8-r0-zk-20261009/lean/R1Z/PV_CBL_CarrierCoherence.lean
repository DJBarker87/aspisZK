import R1Z.PV_CBL_PathTypes
import R1Z.PV_CBL_ShaTypes
namespace R1Z.PV_CBL_CarrierCoherence
open ProverRwFull
set_option autoImplicit false

/-- The independent library carrier refinements commute, so a later wire-up
need not select incompatible copies of any frozen ProverRwFull type. -/
theorem path_sha_commute (base : ExternalTypes) :
    PV_CBL_PathTypes.selectedTypes (PV_CBL_ShaTypes.selectedTypes base) =
      PV_CBL_ShaTypes.selectedTypes (PV_CBL_PathTypes.selectedTypes base) := rfl

theorem blocks_path_unchanged (base : ExternalTypes) :
    PV_CBL_ShaTypes.Blocks (PV_CBL_PathTypes.selectedTypes base) =
      PV_CBL_ShaTypes.Blocks base := rfl

theorem pathbuf_sha_unchanged (base : ExternalTypes) :
    @std.path.PathBuf (PV_CBL_ShaTypes.selectedTypes base) =
      @std.path.PathBuf base := rfl

#print axioms path_sha_commute
#print axioms blocks_path_unchanged
#print axioms pathbuf_sha_unchanged
end R1Z.PV_CBL_CarrierCoherence
