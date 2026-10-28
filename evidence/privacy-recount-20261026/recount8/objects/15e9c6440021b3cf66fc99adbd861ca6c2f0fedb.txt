import R1Z.PV_Join_Canonical5
set_option autoImplicit false
namespace R1Z.PV_Join_RadixBounds5
open PV_Join_Canonical5

theorem canonical_product (a b : Nat) (ha : a < P) (hb : b < P) :
    a*b ≤ (P-1)*(P-1) :=
  Nat.mul_le_mul (by omega) (by omega)

theorem three_products (a b c d e f : Nat)
    (ha : a<P) (hb : b<P) (hc : c<P) (hd : d<P) (he : e<P) (hf : f<P) :
    a*b+c*d+e*f < 2^64 := by
  have ab := canonical_product a b ha hb
  have cd := canonical_product c d hc hd
  have ef := canonical_product e f he hf
  norm_num only [P, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at ab cd ef ⊢
  omega

theorem block_start (block : Nat) (h : block < 7) :
    4*block < 28 ∧ 4*block+1 < 28 ∧ 4*block+2 < 28 ∧ 4*block+3 < 28 := by omega

theorem descending_step (block : Nat) (hp : 0 < block) (hb : block ≤ 6) :
    block-1 < block ∧ block-1 < 7 := by omega

#print axioms canonical_product
#print axioms three_products
#print axioms block_start
#print axioms descending_step
end R1Z.PV_Join_RadixBounds5
