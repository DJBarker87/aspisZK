import NMT_345AfterLength
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
theorem length_call {W : Type} (c : Calls) (s : ProofData W) :
 raw10 c s = (do let n ← c.c4; afterLength c ⟨s,n⟩) := rfl
#print axioms length_call
end NMT_345
