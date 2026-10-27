-- Function body retained verbatim from aeneas-source-op34-ref-002.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_Op34Reference
/-- [pv_cblib_source::empty_reference]:
    Source: 'lib.rs', lines 14:0-14:62
    Visibility: public -/
def empty_reference {T : Type} (v : alloc.vec.Vec T) : Result Bool := do
  let i := alloc.vec.Vec.len v
  ok (i = 0#usize)


#print axioms empty_reference
end PV_CBL_Op34Reference
