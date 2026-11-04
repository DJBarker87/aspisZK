import NFW_PowersCohort
import Lean
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NGU_Carriers
def arr {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def mapR {A B : Type} (f : A → B) (r : Result A) : Result B := do
 let a ← r
 ok (f a)

end NGU_Carriers
