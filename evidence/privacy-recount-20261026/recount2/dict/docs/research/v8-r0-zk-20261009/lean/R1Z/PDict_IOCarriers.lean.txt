import R1Z.PDict_ErrorCarrier
import R1Z.PDict_PathTypesSource
import R1Z.PDict_ReserveErrorSource
set_option autoImplicit false
namespace R1Z.PDict_IOCarriers
open ProverRwFull

/-- Source-extracted path/options/allocation-error carriers. Vec and Layout
use the existing std/Allocator models. File, IO error and formatter stay open;
no native IO effect, descriptor ownership or Drop law is supplied here. -/
@[reducible] def native (base : ExternalTypes) : ExternalTypes :=
  { PDict_ErrorCarrier.native base with
    op1 := PDict_PathTypes.std.fs.OpenOptions
    op2 := PDict_PathTypes.std.path.Path
    op4 := PDict_PathTypes.std.path.PathBuf
    op5 := PDict_ReserveError.alloc.collections.TryReserveError }

theorem type1 (base : ExternalTypes) : (native base).op1 =
    PDict_PathTypes.std.fs.OpenOptions := rfl

theorem type2 (base : ExternalTypes) : (native base).op2 =
    PDict_PathTypes.std.path.Path := rfl

theorem type4 (base : ExternalTypes) : (native base).op4 =
    PDict_PathTypes.std.path.PathBuf := rfl

theorem type5 (base : ExternalTypes) : (native base).op5 =
    PDict_ReserveError.alloc.collections.TryReserveError := rfl

theorem carrier_retraction (base : ExternalTypes) :
    PDict_ErrorCarrier.native (native base) = native base := rfl

@[reducible] noncomputable def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  @PDict_ErrorCarrier.selected (native base) ops

#print axioms type1
#print axioms type2
#print axioms type4
#print axioms type5
#print axioms carrier_retraction
end R1Z.PDict_IOCarriers
