import LPb_CheckpointAttempts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPb_ResultInversion
theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (run : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,run⟩
  | fail e => simp only [bind_tc_fail] at run; cases run
  | div => simp only [bind_tc_div] at run; cases run
#print axioms bind_success
end LPb_ResultInversion
