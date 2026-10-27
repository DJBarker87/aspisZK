import R1Z.PV_CBL_FallbackBoolean
import R1Z.PV_CBL_FallbackAddAlgebra
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalT1
open PV_CBL_FallbackScalar
set_option autoImplicit false
abbrev ch (e f g : U32) : U32 := (e &&& f) ||| ((~~~e) &&& g)
def value (e f g h w : U32) : U32 :=
  U32.wrapping_add (U32.wrapping_add (U32.wrapping_add h (big1 e)) (ch e f g)) w
theorem source (e f g h w : U32) : t1 e f g h w = value e f g h w := by
  unfold t1 value
  rw [PV_CBL_FallbackBoolean.choose_eq]
  rw [PV_CBL_FallbackAddAlgebra.comm _ h]
  rw [← PV_CBL_FallbackAddAlgebra.assoc h _ w,
    ← PV_CBL_FallbackAddAlgebra.assoc h _ (ch e f g)]
#print axioms ch
#print axioms value
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalT1
