import NCV_EqualValue
import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_Equality
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier
/-- The outlined reference equality observes the exact whole byte window.
Every header window is below this bound; no successful-read reply is assumed. -/
theorem value (b v : Slice U8) (cap : b.val.length ≤ 768) :
    NCV_Reference.equal b v = ok (b.val.map byte == v.val.map byte) := by
  classical
  rw [NCV_EqualValue.value b v cap]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact (List.map_inj_right (fun _ _ h => byte_injective h)).symm
#print axioms value
end NMX_R3_Equality
