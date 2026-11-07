import NNH_ResultWp
set_option autoImplicit false
namespace NNH_ResultBindOk
open Aeneas Aeneas.Std Result

theorem value {A B : Type} (raw : Result A) (k : A → Result B) (b : B)
 (success : (raw >>= k)=.ok b) : ∃ a,raw=.ok a ∧ k a=.ok b := by
 cases raw with
 | fail e => simp only [bind_tc_fail] at success; cases success
 | div => simp only [bind_tc_div] at success; cases success
 | ok a => exact ⟨a,rfl,by simpa only [bind_tc_ok] using success⟩
#print axioms value
end NNH_ResultBindOk
