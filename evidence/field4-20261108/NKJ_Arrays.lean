import NKJ_Loop
import NGA_Wrappers
set_option autoImplicit false
namespace NKJ_Arrays
open Aeneas Aeneas.Std Result
abbrev Q := NGA_Cache.Q

def encode {n : Usize} (xs : Array Q n) : Array NKJ_Extracted.field.QM31 n :=
 ⟨xs.val.map NKJ_Extracted.fromCanonical,by simpa using xs.property⟩

end NKJ_Arrays
