import NMT_345Select
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Third index occurrence, after the first two exact reads. -/
def selectCheckpoint {W : Type} (s : Parent W) (proof pub : Account)
 (next : Selected W → Result Ret) : Result Ret := do
 let checkpoint ← Slice.index_usize s.accounts 2#usize
 next ⟨s,proof,pub,checkpoint⟩
theorem select_checkpoint_call {W : Type} (s : Parent W) (proof pub : Account)
 (next : Selected W → Result Ret) :
 selectCheckpoint s proof pub next =
 (Slice.index_usize s.accounts 2#usize >>= fun checkpoint => next ⟨s,proof,pub,checkpoint⟩) := rfl
#print axioms select_checkpoint_call
end NMT_345
