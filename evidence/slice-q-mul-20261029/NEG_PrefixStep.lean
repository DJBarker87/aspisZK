import NEG_PrefixAssociation
import ExtractedCurrentReducer
set_option autoImplicit false
noncomputable section
namespace NEG_PrefixStep
open Aeneas Aeneas.Std Result AspisR1
/-- No canonical-input precondition is needed by this actual emitted M31 call. -/
theorem multiply (a b : U32) :
    ∃ z : U32, NEG_PrefixFull.aspis_core.field.M31.mul a b = ok z ∧
      z.val = (a.val*b.val)%2147483647 ∧ z.val<2147483647 := by
  exact ExtractedCurrentReducer.current_mul_mod a b
#print axioms multiply
#print alloc.vec.Vec.push
end NEG_PrefixStep
end
