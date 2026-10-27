-- Exact extracted body; generated Types is empty, no external template.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_StringPushBytes
/-- [pv_cblib_source::push_bytes_reference]:
    Source: 'lib.rs', lines 385:0-385:76
    Visibility: public -/
def push_bytes_reference
  (s : alloc.vec.Vec Std.U8) (t : Slice Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 s t

#print axioms push_bytes_reference
end PV_CBL_StringPushBytes
