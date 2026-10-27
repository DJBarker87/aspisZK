import S7OwnedP6ScalarProof
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSg_PhaseNat
open AspisR1BatchedFoldSourceStep
/-- The periodic bound is preserved by one canonical product, for arbitrary
transaction ordinals. This is the scalar invariant used inside the row loop. -/
theorem source (terms raw a b : Nat) (ha : a<2^31-1) (hb : b<2^31-1)
 (hr : raw<2^34+(terms%4)*(2^31-2)^2) :
 sourcePush terms raw (a*b)<2^34+((terms+1)%4)*(2^31-2)^2 := by
 have product := product_bound ha hb
 change a*b≤(2^31-2)^2 at product
 have phase : terms%4<4 := Nat.mod_lt _ (by decide)
 have safe : raw+a*b<2^64 := by
  have h := Nat.mul_le_mul_right ((2^31-2)^2) (show terms%4≤3 by omega)
  omega
 unfold sourcePush
 split
 · have folded := fold_lt_two34 safe
   omega
 · have next : (terms+1)%4=terms%4+1 := by omega
   rw [next]
   omega
#print axioms source
end XSg_PhaseNat
