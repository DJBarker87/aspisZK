import XRq_ByteEquation
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRq_ByteCarrier
/-- Isolated carrier reduction after L097's looping simplifier timeout. -/
theorem val (b : BitVec 8) : (b#uscalar : U8).val = b.toNat := rfl
#print axioms val
end XRq_ByteCarrier
