import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockBindExt
set_option autoImplicit false
theorem bind_ext {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) := congrArg (fun k => r >>= k) (funext h)
#print axioms bind_ext
end R1Z.PV_CBL_BlockBindExt
