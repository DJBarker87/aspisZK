import R1Z.PV_CBL_PathTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_StringViewTypes
open ProverRwFull
set_option autoImplicit false
/-- Owned String represents both PathBuf and its Path view on this selection.
The prior opaque PathBuf selection remains available under its stable names. -/
@[reducible] def base (b : ExternalTypes) : ExternalTypes := {b with op4 := String}
@[reducible] def Types (b : ExternalTypes) : ExternalTypes :=
  PV_CBL_PathTypes.selectedTypes (base b)
theorem path (b : ExternalTypes) : @std.path.Path (Types b) = String := rfl
theorem pathbuf (b : ExternalTypes) : @std.path.PathBuf (Types b) = String := rfl
#print axioms path
#print axioms pathbuf
end R1Z.PV_CBL_StringViewTypes
