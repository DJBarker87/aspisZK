import R1Z.PV_CBL_StringByteObservation
import R1Z.PV_CBL_CapacityBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_AppendSource
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]
/-- P6 byte-reference adapter. Native domain/bounds and allocation effects
are recorded separately; this is not an unbounded machine refinement. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op31 := PV_CBL_StringBytesAdapter.append}
theorem op31_source (ops : ExternalFuns) (s : String) (t : Str) :
    (selected ops).op31 s t = PV_CBL_StringBytesAdapter.append s t := rfl
#print axioms op31_source
end R1Z.PV_CBL_AppendSource
