import NFF_BaseMultiply
set_option autoImplicit false
namespace AspisR1.NFF_QueryProduct
open Aeneas Aeneas.Std Result
/-- Natural node-product reply and downstream canonicality, from the copied
coherent existing source law; no multiplication is proved in Kani. -/
theorem emitted (z : U32) : ∃ reply : U32,
    FIo_Native.aspis_core.field.M31.mul z z=ok reply ∧
    reply.val=(z.val*z.val)%2147483647 ∧ reply.val<2147483647 :=
  NFF_BaseMultiply.source z z
#print axioms emitted
end AspisR1.NFF_QueryProduct
