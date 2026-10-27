import R1Z.PV_CBL_FallbackBoolean
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalT2
open PV_CBL_FallbackScalar
set_option autoImplicit false
abbrev maj (a b c : U32) : U32 := (a &&& b) ||| (a &&& c) ||| (b &&& c)
def value (a b c : U32) : U32 := U32.wrapping_add (big0 a) (maj a b c)
theorem source (a b c : U32) : t2 a b c = value a b c := by
  unfold t2 value
  rw [PV_CBL_FallbackBoolean.majority_eq]
#print axioms maj
#print axioms value
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalT2
