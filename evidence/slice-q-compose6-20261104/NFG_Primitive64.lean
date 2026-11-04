import NFF_ProductCall
import NEG_MachineProduct
set_option autoImplicit false
namespace AspisR1.NFG_Primitive64
open Aeneas Aeneas.Std
def reply (a b : U64) : U64 := UScalar.wrapping_mul a b
theorem law : NFF_ProductCall.Law reply := by
 intro a b ha hb
 exact NEG_MachineProduct.u64_value a b
#print axioms law
end AspisR1.NFG_Primitive64
