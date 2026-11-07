import NMT_345Frames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Separate public getter occurrence after zero-check, at ORIGINAL account1. -/
def publicDataStep {W : Type} (s : CheckpointData W) (next : PublicData W → Result Ret) : Result Ret :=
 tryStep (dataCall s.publicAccount) (fun bytes => next ⟨s,bytes⟩)
theorem publicData_std {W : Type} (s : CheckpointData W) (next : PublicData W → Result Ret) :
 publicDataStep s next = match s.publicAccount.bytes with
 | .Ok bytes => next ⟨s,bytes.deref⟩
 | .Err error => .ok (.Err error) := by
 unfold publicDataStep
 rw [data_std]
 cases s.publicAccount.bytes <;> rfl
#print axioms publicData_std
end NMT_345
