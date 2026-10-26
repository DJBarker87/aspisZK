import SdkC_Source
set_option autoImplicit false
namespace AspisR1.F3V_CheckpointCongr
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

theorem bind {A B : Type} (p q : Code A) (f g : A → Code B)
    (first : p=q) (next : ∀ a,f a=g a) : (p >>= f)=(q >>= g) := by
  rw [first]
  exact congrArg (fun k => q >>= k) (funext next)

#print axioms bind
end AspisR1.F3V_CheckpointCongr
