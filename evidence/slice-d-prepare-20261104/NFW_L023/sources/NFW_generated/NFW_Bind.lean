import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace AspisR1.NFW_Bind
open Aeneas Aeneas.Std Result
theorem same {α β : Type} (m : Result α) (f g : α→Result β)
 (h : ∀ x,f x=g x) : (m >>= f)=(m >>= g) :=
 congrArg (fun k=>m >>= k) (funext h)
#print axioms same
end AspisR1.NFW_Bind
