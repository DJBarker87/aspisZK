import AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PreparePure
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

theorem right {A B : Type} (r : Result A) (k : A → Code B) (out : B)
    (success : erase ((monadLift r : Code A) >>= k)=ok out) :
    ∃ a,r=ok a ∧ erase (k a)=ok out ∧
      (run ((monadLift r : Code A) >>= k)).1=(run (k a)).1 := by
  cases r with
  | fail e=>cases success
  | div=>cases success
  | ok a=>exact ⟨a,rfl,success,rfl⟩

#print axioms right
end AspisR1.F3Q_PreparePure
end
