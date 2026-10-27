-- Draft; retain verbatim fresh extracted body before claiming source credit.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_PathBytesReference

def path_bytes_reference (v : alloc.vec.Vec U8) : Result (alloc.vec.Vec U8) :=
  ok v
#print axioms path_bytes_reference
end PV_CBL_PathBytesReference
