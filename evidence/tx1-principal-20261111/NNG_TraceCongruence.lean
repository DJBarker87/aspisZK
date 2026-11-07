import NNG_TraceAlgebra
set_option autoImplicit false
namespace AspisR1.NNG_TraceCongruence
open Aeneas Aeneas.Std Result NMT_CallTree
/-- Tell the simplifier to visit symbolic Result continuations. No reply
value is evaluated or selected; all three outer constructors remain possible. -/
@[congr] theorem result_bind {A B : Type} (r : Result A) (f g : A → Result B)
    (tail : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  result_congr r f g tail
#print axioms result_bind
end AspisR1.NNG_TraceCongruence
