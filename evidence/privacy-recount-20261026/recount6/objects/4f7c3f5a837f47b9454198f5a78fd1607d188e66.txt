-- Exact extracted body; generated Types is empty, no external template.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_StringCapacityBytes
/-- [pv_cblib_source::string_capacity_bytes_reference]:
    Source: 'lib.rs', lines 383:0-383:70
    Visibility: public -/
def string_capacity_bytes_reference
  (_n : Std.Usize) : Result (alloc.vec.Vec Std.U8) := do
  ok (alloc.vec.Vec.new Std.U8)

#print axioms string_capacity_bytes_reference
end PV_CBL_StringCapacityBytes
