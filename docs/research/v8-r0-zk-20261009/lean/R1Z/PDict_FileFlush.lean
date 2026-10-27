import R1Z.PDict_VolatileCell
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FileFlush
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_VolatileCell.native
section Value
variable [ExternalTypes]
/-- Unix std File::flush is an unconditional success, preserving the borrowed
File owner. P6 checks its full scalar descriptor outcome/frame. No native
File representation, close, sync_all, write, or IO-world law is asserted here. -/
def flush (file : std.fs.File) :
    Result ((core.result.Result Unit std.io.error.Error) × std.fs.File) :=
  .ok (.Ok (),file)
end Value
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_VolatileCell.selected base ops with op17 := flush }

theorem op17_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (file : (native base).op0) :
    (selected base ops).op17 file = .ok (.Ok (),file) := rfl

theorem owner_preserved [ExternalTypes] (file : std.fs.File) :
    (do let (_,next) ← flush file; .ok next) = .ok file := rfl

#print axioms op17_installed
#print axioms owner_preserved
end R1Z.PDict_FileFlush
