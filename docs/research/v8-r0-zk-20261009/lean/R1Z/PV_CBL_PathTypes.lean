import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PathTypes
open ProverRwFull
set_option autoImplicit false

/-- A path view is represented by its owned PathBuf carrier. The existing
opaque PathBuf carrier is retained, with no byte-layout or UTF-8 restriction.
Native view/owner association is separate P6 evidence, not a world instance. -/
@[reducible] def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  { base with op2 := base.op4 }

theorem path_carrier (base : ExternalTypes) :
    @std.path.Path (selectedTypes base) = @std.path.PathBuf base := rfl

theorem pathbuf_carrier (base : ExternalTypes) :
    @std.path.PathBuf (selectedTypes base) = @std.path.PathBuf base := rfl

#print axioms path_carrier
#print axioms pathbuf_carrier
end R1Z.PV_CBL_PathTypes
