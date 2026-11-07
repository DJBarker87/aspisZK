import NMT_345SelectCheckpoint
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Second occurrence; the third occurrence remains a named continuation. -/
def selectPublic {W : Type} (s : Parent W) (proof : Account)
 (next : Selected W → Result Ret) : Result Ret := do
 let pub ← Slice.index_usize s.accounts 1#usize
 selectCheckpoint s proof pub next
theorem select_public_call {W : Type} (s : Parent W) (proof : Account)
 (next : Selected W → Result Ret) :
 selectPublic s proof next =
 (Slice.index_usize s.accounts 1#usize >>= fun pub => selectCheckpoint s proof pub next) := rfl
#print axioms select_public_call
end NMT_345
