import NDN_RawProductBridge
import NDN_ArithmeticBounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_InterpolationPrestate

theorem raw_domain (a0 a1 a2 b0 b1 b2 : U32)
 (ha0:a0.val<2147483647) (ha1:a1.val<2147483647) (ha2:a2.val<2147483647)
 (hb0:b0.val<2147483647) (hb1:b1.val<2147483647) (hb2:b2.val<2147483647) :
 ∃ p0 p1 p2 : U64,
 (core.convert.num.FromU64U32.from a0 * core.convert.num.FromU64U32.from b0)=ok p0 ∧
 (core.convert.num.FromU64U32.from a1 * core.convert.num.FromU64U32.from b1)=ok p1 ∧
 (core.convert.num.FromU64U32.from a2 * core.convert.num.FromU64U32.from b2)=ok p2 ∧
 p0.val=a0.val*b0.val ∧ p1.val=a1.val*b1.val ∧ p2.val=a2.val*b2.val ∧
 p0.val≤2147483646^2 ∧ p1.val≤2147483646^2 ∧ p2.val≤2147483646^2 ∧
 p0.val+p1.val+p2.val<2^64 := by
 obtain ⟨p0,h0,v0⟩:=NDN_RawProductBridge.product a0 b0 ha0 hb0
 obtain ⟨p1,h1,v1⟩:=NDN_RawProductBridge.product a1 b1 ha1 hb1
 obtain ⟨p2,h2,v2⟩:=NDN_RawProductBridge.product a2 b2 ha2 hb2
 have b0' : a0.val*b0.val≤2147483646^2 := by
  simpa only [pow_two] using Nat.mul_le_mul (show a0.val≤2147483646 by omega) (show b0.val≤2147483646 by omega)
 have b1' : a1.val*b1.val≤2147483646^2 := by
  simpa only [pow_two] using Nat.mul_le_mul (show a1.val≤2147483646 by omega) (show b1.val≤2147483646 by omega)
 have b2' : a2.val*b2.val≤2147483646^2 := by
  simpa only [pow_two] using Nat.mul_le_mul (show a2.val≤2147483646 by omega) (show b2.val≤2147483646 by omega)
 refine ⟨p0,p1,p2,h0,h1,h2,v0,v1,v2,?_,?_,?_,?_⟩
 · simpa only [v0] using b0'
 · simpa only [v1] using b1'
 · simpa only [v2] using b2'
 · rw [v0,v1,v2]
   exact NDN_ArithmeticBounds.three_products _ _ _ _ _ _ ha0 hb0 ha1 hb1 ha2 hb2

#print axioms raw_domain
end NDN_InterpolationPrestate
