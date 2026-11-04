import NFB_MulDischarge
import NEW_GeometryArithmetic
set_option autoImplicit false
namespace AspisR1.NFF_QueryProduct
open Aeneas Aeneas.Std Result

/-- The incoming caller's saved node-product reply has its exact natural
value and downstream canonical domain from the emitted multiplication.
Sibling multiplication proof is imported, not duplicated. -/
theorem emitted (z : U32) : ∃ reply : U32,
    FIo_Native.aspis_core.field.M31.mul z z=ok reply ∧
    reply.val=(z.val*z.val)%2147483647 ∧ reply.val<2147483647 := by
  obtain ⟨reply,run,value,canonical⟩:=NFB_MulDischarge.multiplication z z
  exact ⟨reply,(NEW_GeometryArithmetic.multiply z z).symm.trans run,value,canonical⟩

#print axioms emitted
end AspisR1.NFF_QueryProduct
