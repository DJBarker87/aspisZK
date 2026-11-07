import NGT_NBL_CodeRunLaws
set_option autoImplicit false
namespace LIBC_CodeMonad
open Aeneas Aeneas.Std Result AspisR1PublicPreparation.PreparedHashCode
theorem bind_assoc {A B C : Type} (p : Code A) (f : A → Code B) (g : B → Code C) :
 bind (bind p f) g = bind p (fun a => bind (f a) g) := by
 induction p with
 | done a => rfl
 | step r k ih => exact congrArg (Code.step r) (funext ih)
 | digest D hash parts k ih => exact congrArg (Code.digest D hash parts) (funext ih)
theorem pure_right {A : Type} (p : Code A) : bind p Code.done = p := by
 induction p with
 | done a => rfl
 | step r k ih => exact congrArg (Code.step r) (funext ih)
 | digest D hash parts k ih => exact congrArg (Code.digest D hash parts) (funext ih)
#print axioms bind_assoc
#print axioms pure_right
end LIBC_CodeMonad
