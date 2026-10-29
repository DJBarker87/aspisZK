import PV_L1D_CountSuccess
set_option autoImplicit false
namespace PV_L1D_SelectedCount
open R1Z.SideChannelL1AttemptRecord
open R1Z.ProverCommitRetry34 (Published)
variable {S P A : Type}
/-- Value-level interpretation of the deployed Accounts::selected guard.
JSON formatting, array ownership and error allocation are not erased by a
native-association claim: this module makes no such claim. -/
def selected (keys : Fin 8 → A) (attempts entered : Nat) : Option (Nat × A) :=
  if h : 1 ≤ attempts ∧ attempts ≤ 8 ∧ attempts = entered then
    some (attempts-1, keys ⟨attempts-1,by omega⟩)
  else none

theorem original_success (owner : Owner S P) (s : S) (p : Published P)
    (keys : Fin 8 → A) (h : (run owner 8 0 s).1.result = .done p) :
    ∃ k : Fin 8, k.val = p.attempts-1 ∧
      selected keys p.attempts (run owner 8 0 s).1.attempts.length = some (k.val,keys k) := by
  obtain ⟨lower,upper⟩ := PV_L1D_CountSuccess.count_bounds owner s p h
  have count := PV_L1D_CountSuccess.count_eq_entered owner 8 0 s p h
  have entered : p.attempts = (run owner 8 0 s).1.attempts.length := by omega
  refine ⟨⟨p.attempts-1,by omega⟩,rfl,?_⟩
  have guard : 1 ≤ p.attempts ∧ p.attempts ≤ 8 ∧ p.attempts = (run owner 8 0 s).1.attempts.length := ⟨lower,upper,entered⟩
  simp only [selected,dif_pos guard]
#print axioms original_success
end PV_L1D_SelectedCount
