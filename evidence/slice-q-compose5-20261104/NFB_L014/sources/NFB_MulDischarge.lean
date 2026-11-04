import NEW_GeometryPolynomial
set_option autoImplicit false
namespace NFB_MulDischarge
open Aeneas Aeneas.Std Result AspisR1

/-- Every raw scalar operand is admitted. The complete emitted operation
returns ok with precisely the natural-number product specification and a
canonical reply. This discharges the local ordered-log product abstraction. -/
theorem multiplication (left right : U32) :
    ∃ reply : U32,
      NEW_GeometryActual.aspis_core.field.M31.mul left right=ok reply ∧
      reply.val=(left.val*right.val)%2147483647 ∧ reply.val<2147483647 := by
 obtain ⟨reply,run,value,canonical⟩ := ExtractedCurrentReducer.current_mul_mod left right
 exact ⟨reply,(NEW_GeometryArithmetic.multiply_probe left right).trans run,value,canonical⟩

/-- The caller's only numeric restriction on its arbitrary native product
reply is supplied by the operation above, for all possible raw line words. -/
theorem caller_product_domain (line : U32) :
    ∃ reply : U32,
      NEW_GeometryActual.aspis_core.field.M31.mul line line=ok reply ∧
      reply.val<2147483647 := by
 obtain ⟨reply,run,_,canonical⟩ := multiplication line line
 exact ⟨reply,run,canonical⟩

/-- Reuse NEW's contextual substitution; the downstream double/subtract
preconditions are derived from the SAME saved product, never caller premises. -/
theorem row_continuation {T : Type} (line : U32) (k : U32 → Result T) :
 (do let p ← NEW_GeometryActual.aspis_core.field.M31.mul line line
     let d ← NEW_GeometryActual.aspis_core.field.M31.double p
     let z ← NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE
     k z) =
 (do let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul line line
     let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
     let z ← AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32
     k z) := NEW_GeometryPolynomial.continuation line k

#print axioms multiplication
#print axioms caller_product_domain
#print axioms row_continuation
end NFB_MulDischarge
