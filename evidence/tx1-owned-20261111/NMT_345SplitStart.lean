import NMT_345AfterLength
import NMT_345AfterStart
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
theorem start_call {W : Type} (c : Calls) (s : HasLength W) :
 afterLength c s = (do let n ← c.c8; afterStart c ⟨s,n⟩) := rfl
#print axioms start_call
end NMT_345
