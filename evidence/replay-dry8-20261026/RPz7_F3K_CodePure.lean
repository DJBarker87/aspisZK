import RPz7_F3K_CodeBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CodePure
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem invert {A B : Type} (m : Result A) (k : A → Code B) (v : B)
    (h : erase (PreparedHashCode.bind (monadLift m) k)=ok v) :
    ∃ a,m=ok a ∧ erase (k a)=ok v ∧
      observe (run (PreparedHashCode.bind (monadLift m) k)).1=observe (run (k a)).1 := by
  cases m with
  | ok a => exact ⟨a,rfl,h,rfl⟩
  | fail e => cases h
  | div => cases h

#print axioms invert
end AspisR1.F3K_CodePure
end
