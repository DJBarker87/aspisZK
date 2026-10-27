import XRq_AddValue
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRq_SubCompose
open XRp_PowersScalarSub
/-- Numeric-free bind stage, separated after XRq_L071 kernel memory rejection. -/
theorem compose (a b p : U32) (ha : a.val+p.val<4294967296)
 (hb : b.val ≤ (U32.wrapping_add a p).val) :
 wrappingSub (U32.wrapping_add a p) b = (do let x ← a+p; checkedSub x b) := by
 rw [XRp_CheckedWrapping.add a p ha]
 exact subtract _ _ hb
#print axioms compose
end XRq_SubCompose
