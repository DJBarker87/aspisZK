import NGD_ParseReference
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_Monad
theorem bind_congr {α β : Type} (r : Result α) (left right : α→Result β)
 (law : ∀ x,left x=right x) : (r >>= left)=(r >>= right) :=
 congrArg (fun k=>r >>= k) (funext law)
theorem bind_congr_on {α β : Type} (r : Result α) (left right : α→Result β)
 (law : ∀ x,r=ok x→left x=right x) : (r >>= left)=(r >>= right) := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok x => exact law x rfl
#print axioms bind_congr
#print axioms bind_congr_on
end NGV_Monad
