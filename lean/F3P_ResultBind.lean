import F3P_SemanticDecode
set_option autoImplicit false
namespace AspisR1.F3P_ResultBind
open Aeneas Aeneas.Std Result

theorem success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k)=ok out) : ∃ a,m=ok a ∧ k a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => cases h
  | div => cases h

#print axioms success
end AspisR1.F3P_ResultBind
