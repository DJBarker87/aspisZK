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
 ext <;> simp [cmProduct,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,sub_eq_add_neg]

theorem rotation (a : CM31Exact) : rotate a=qm31R*a := by
 ext <;> simp [rotate,qm31R,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

theorem tower_product (a b : QM31Exact) : towerProduct a b=a*b := by
 ext <;> simp [towerProduct,cm_product,rotation,qm31R,
  QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

theorem base_add (a b : M31Exact) : (a+b).val=(a.val+b.val)%P := by
 exact ZMod.val_add a b

theorem base_mul (a b : M31Exact) : (a*b).val=(a.val*b.val)%P := by
 exact ZMod.val_mul a b

theorem base_sub (a b : M31Exact) : (a-b).val=(a.val+P-b.val)%P := by
 have hb : b.val ≤ a.val+P := by have h:=ZMod.val_lt b;omega
 have hn : ((a.val+P-b.val : Nat) : M31Exact)=a-b := by
  rw [Nat.cast_sub hb]
  simp only [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,add_zero]
 rw [←hn]
 simp only [ZMod.val_natCast]

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
