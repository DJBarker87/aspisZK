import NGH_AccumulateRef
import NFT_Dot
set_option autoImplicit false
namespace NGH_ProductStub
open Aeneas Aeneas.Std Result NGA_Cell

theorem primitive (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
 ∃ p : U64, UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)=ok p ∧
 p.val=a.val*b.val ∧ p.val≤(2147483647-1)^2 := by
 obtain ⟨p,ho,hv⟩ := NFT_Dot.scalar_product a b ha hb
 refine ⟨p,ho,hv,?_⟩
 rw [hv,pow_two]
 exact Nat.mul_le_mul (by omega) (by omega)

theorem canonical_cache (left right : Cache)
 (hl : NGA_CacheDomain.Bounded left) (hr : NGA_CacheDomain.Bounded right) (c : Cell) :
 ∃ p : U64,
 UScalar.mul (UScalar.cast .U64 (get left c)) (UScalar.cast .U64 (get right c))=ok p ∧
 p.val=(get left c).val*(get right c).val ∧ p.val≤(2147483647-1)^2 :=
 primitive _ _ (NGA_Step.bounded_get left hl c) (NGA_Step.bounded_get right hr c)

#print axioms primitive
#print axioms canonical_cache
end NGH_ProductStub
