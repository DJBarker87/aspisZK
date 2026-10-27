-- Definition retained verbatim from aeneas-source-path-ref-opt-final-support-02.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_PathBytesReference
/-- [pv_cblib_source::path_bytes_reference]:
    Source: 'lib.rs', lines 42:0-42:56
    Visibility: public -/
def path_bytes_reference
  (v : alloc.vec.Vec Std.U8) : Result (alloc.vec.Vec Std.U8) := do
  ok v

#print axioms path_bytes_reference
end PV_CBL_PathBytesReference
