-- Body/signature retained from aeneas-source-op35-ref-003.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_Op35Reference
/-- [pv_cblib_source::default_reference]:
    Source: 'lib.rs', lines 15:0-15:54
    Visibility: public -/
def default_reference (T : Type) : Result (alloc.vec.Vec T) := do
  ok (alloc.vec.Vec.new T)


#print axioms default_reference
end PV_CBL_Op35Reference
