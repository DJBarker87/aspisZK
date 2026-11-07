import NMT_345SelectPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- First occurrence factors the existing exact selector into the separately
checked second and third occurrences, carrying the original parent. -/
theorem select_proof_call {W : Type} (s : Parent W) (next : Selected W → Result Ret) :
 select s next = (Slice.index_usize s.accounts 0#usize >>= fun proof => selectPublic s proof next) := rfl
#print axioms select_proof_call
end NMT_345
