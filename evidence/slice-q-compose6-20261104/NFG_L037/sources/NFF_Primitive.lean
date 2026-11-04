import NFF_LoggedEight
import NEG_MachineProduct
set_option autoImplicit false
namespace AspisR1.NFF_Primitive
open Aeneas Aeneas.Std

def reply (a b : U32) : U64 :=
  UScalar.wrapping_mul (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from b)

/-- Actual widened primitive semantics discharge the log law; it is not an
extra assumption about an arbitrarily selected whole-callee reply. -/
theorem law : NFF_LoggedEight.Law reply := by
  intro a b ha hb
  have h:=NEG_MachineProduct.u64_value
    (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from b)
  have av : (core.convert.num.FromU64U32.from a).val=a.val := by scalar_tac
  have bv : (core.convert.num.FromU64U32.from b).val=b.val := by scalar_tac
  simpa only [reply,av,bv] using h

#print axioms law
end AspisR1.NFF_Primitive
