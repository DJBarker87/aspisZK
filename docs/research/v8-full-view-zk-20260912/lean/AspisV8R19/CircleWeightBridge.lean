import AspisV8R19.SourceEncodedOpening
import AspisFormal.V5FriNaturalBasisRadix4
import Mathlib.Data.Nat.Bitwise

/-! Bit-selected source factors equal the interleaved natural circle basis.
The selector inventory is proved symbolically, without enumerating 1024 rows. -/
namespace AspisR19.CircleWeightBridge
open AspisCircleTensorBinding SourceEncodedOpening
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def factor (x y : F) : Nat → F
  | 0 => y
  | n+1 => doubledFactor x n

theorem factor_step (x y : F) (n : Nat) :
    factor x y (n+2)=2*(factor x y (n+1))^2-1 := by rfl

theorem bit_product_even (x y : F) (n : Nat) :
    (∏ b ∈ (2*n).bitIndices.toFinset, factor x y b)=naturalLineValue x n := by
  have hm (xs : List Nat) : (xs.map (fun b => b+1)).toFinset=xs.toFinset.image (fun b => b+1) := by
    ext b; simp
  rw [Nat.bitIndices_two_mul,hm,Finset.prod_image]
  · rfl
  · intro i _ j _ h; exact Nat.add_right_cancel h

theorem bit_product_odd (x y : F) (n : Nat) :
    (∏ b ∈ (2*n+1).bitIndices.toFinset, factor x y b)=y*naturalLineValue x n := by
  have hm (xs : List Nat) : (xs.map (fun b => b+1)).toFinset=xs.toFinset.image (fun b => b+1) := by
    ext b; simp
  rw [Nat.bitIndices_two_mul_add_one,List.toFinset_cons,hm,
    Finset.prod_insert (by simp),Finset.prod_image]
  · rfl
  · intro i _ j _ h; exact Nat.add_right_cancel h

theorem bit_product (x y : F) (r : Nat) :
    (∏ b ∈ r.bitIndices.toFinset, factor x y b)=circleWeight x y r := by
  by_cases h : r%2=0
  · have he : r=2*(r/2) := by omega
    rw [he,bit_product_even]
    simp only [circleWeight,show (2*(r/2))/2=r/2 by omega,
      show (2*(r/2))%2=0 by omega,↓reduceIte,mul_one]
  · have he : r=2*(r/2)+1 := by omega
    rw [he,bit_product_odd]
    simp only [circleWeight,show (2*(r/2)+1)/2=r/2 by omega,
      show (2*(r/2)+1)%2=1 by omega,show ¬(1:Nat)=0 by decide,↓reduceIte]
    ring

theorem selector_bit (r b : Nat) : r &&& (1 <<< b) ≠ 0 ↔ r.testBit b := by
  rw [Nat.shiftLeft_eq,one_mul,Nat.and_two_pow]
  cases h : r.testBit b <;> simp [h]

theorem selector_eq (r : Nat) (hr : r<1024) :
    r.bitIndices.toFinset=(Finset.range 10).filter (fun b => r &&& (1 <<< b) ≠ 0) := by
  ext b
  simp only [List.mem_toFinset,Nat.mem_bitIndices,Finset.mem_filter,Finset.mem_range,selector_bit]
  constructor
  · intro hb
    refine ⟨?_,hb⟩
    have hp := Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr hb)
    by_contra hn
    have hpow : 2^10 ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact And.right

def sourceWeight (x y : F) (r : Nat) : F :=
  ∏ b ∈ (Finset.range 10).filter (fun b => r &&& (1 <<< b) ≠ 0), factor x y b

theorem sourceWeight_eq (x y : F) (r : Nat) (hr : r<1024) :
    sourceWeight x y r=circleWeight x y r := by
  rw [sourceWeight,← selector_eq r hr,bit_product]

theorem circle_four (x y : F) (n : Nat) (k : Fin 4) :
    circleWeight x y (4*n+k.val)=
      naturalLineValue (doubledFactor x 1) n * ![1,y,x,x*y] k := by
  have hd0 : (4*n)/2=2*n := by omega
  have hd1 : (4*n+1)/2=2*n := by omega
  have hd2 : (4*n+2)/2=2*n+1 := by omega
  have hd3 : (4*n+3)/2=2*n+1 := by omega
  have hm0 : (4*n)%2=0 := by omega
  have hm1 : (4*n+1)%2=1 := by omega
  have hm2 : (4*n+2)%2=0 := by omega
  have hm3 : (4*n+3)%2=1 := by omega
  fin_cases k <;> simp [add_zero,
    circleWeight,hd0,hd1,hd2,hd3,hm0,hm1,hm2,hm3,show ¬(1:Nat)=0 by decide,
    ↓reduceIte,AspisV5FriNaturalBasisRadix4.naturalLineValue_two_mul,
    AspisV5FriNaturalBasisRadix4.naturalLineValue_two_mul_add_one,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,mul_one]
    <;> ring

#print axioms factor_step
#print axioms bit_product_even
#print axioms bit_product_odd
#print axioms bit_product
#print axioms selector_bit
#print axioms selector_eq
#print axioms sourceWeight_eq
#print axioms circle_four
end
end AspisR19.CircleWeightBridge
