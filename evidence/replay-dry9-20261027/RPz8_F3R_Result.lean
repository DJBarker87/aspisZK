import RPz8_F3Q_PreparePure
set_option autoImplicit false
namespace AspisR1.F3R_Result
open Aeneas Aeneas.Std Result

theorem bind_success {A B : Type} (r : Result A) (k : A → Result B) (out : B)
    (success : (r >>= k)=ok out) : ∃ a,r=ok a ∧ k a=ok out := by
  cases r with
  | ok a=>exact ⟨a,rfl,success⟩
  | fail e=>cases success
  | div=>cases success

#print axioms bind_success
end AspisR1.F3R_Result
