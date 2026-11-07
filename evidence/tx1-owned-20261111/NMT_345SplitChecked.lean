import NMT_345AfterStart
import NMT_345AfterSum
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
theorem checked_call {W : Type} (c : Calls) (s : HasStart W) :
 afterStart c s = (do let sum ← lift (Usize.checked_add s.proofStart s.proofLength); afterSum c ⟨s,sum⟩) := rfl
#print axioms checked_call
end NMT_345
