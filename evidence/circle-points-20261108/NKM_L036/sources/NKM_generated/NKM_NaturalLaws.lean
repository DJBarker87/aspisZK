import NKM_SpecLaws
set_option autoImplicit false
noncomputable section
namespace NKM_NaturalLaws
open AspisV8R15.ExactTowerBase

def cmProduct (a b : CM31Exact) : CM31Exact := ⟨a.re*b.re-a.im*b.im,a.re*b.im+a.im*b.re⟩
def rotate (a : CM31Exact) : CM31Exact := ⟨a.re+a.re-a.im,a.re+(a.im+a.im)⟩
def towerProduct (a b : QM31Exact) : QM31Exact :=
 ⟨cmProduct a.re b.re+rotate (cmProduct a.im b.im),cmProduct a.re b.im+cmProduct a.im b.re⟩

theorem cm_product (a b : CM31Exact) : cmProduct a b=a*b := by
 ext <;> simp [cmProduct,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]

theorem rotation (a : CM31Exact) : rotate a=qm31R*a := by
 ext <;> simp [rotate,qm31R,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

theorem tower_product (a b : QM31Exact) : towerProduct a b=a*b := by
 ext <;> simp only [towerProduct,cm_product,rotation,QuadraticAlgebra.re_mk,QuadraticAlgebra.im_mk,
  QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
  QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,mul_zero,zero_mul,add_zero] <;> ring

theorem base_add (a b : M31Exact) : (a+b).val=(a.val+b.val)%P := by
 exact ZMod.val_add a b

theorem base_mul (a b : M31Exact) : (a*b).val=(a.val*b.val)%P := by
 exact ZMod.val_mul a b

theorem base_sub (a b : M31Exact) : (a-b).val=(a.val+P-b.val)%P := by
 exact ZMod.val_sub a b

/-- The wrapping operations in the assumed natural specification agree with natural arithmetic on the full canonical domain. -/
theorem base_bounds (a b : Nat) (ha : a<P) (hb : b<P) :
 a+b<2^64 ∧ b≤a+P ∧ a+P<2^64 ∧ a*b<2^64 := by
 have hm : a*b≤P*P := Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hb)
 norm_num [P] at ha hb hm ⊢
 omega

#print axioms cm_product
#print axioms rotation
#print axioms tower_product
#print axioms base_add
#print axioms base_mul
#print axioms base_sub
#print axioms base_bounds
end NKM_NaturalLaws
end
