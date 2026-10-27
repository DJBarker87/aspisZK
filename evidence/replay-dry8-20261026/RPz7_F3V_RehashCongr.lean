import RPz7_F3U_RehashBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_RehashCongr
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode

theorem bind {A B : Type} (H : Bytes → State) (p q : Code A)
    (f g : A → Code B) (first : F3U_Rehash.code H p=q)
    (next : ∀ a,F3U_Rehash.code H (f a)=g a) :
    F3U_Rehash.code H (p >>= f)=(q >>= g) := by
  rw [F3U_RehashBind.bind,first]
  exact congrArg (fun k => q >>= k) (funext next)

#print axioms bind
end AspisR1.F3V_RehashCongr
end
