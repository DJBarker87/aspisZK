import R1Z.PV_OWNK_CMDecode
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_QMDecode
open PV_OWNK_TowerCanon
abbrev K := AspisV8R15.ExactTowerBase.QM31Exact
abbrev dc := PV_OWNK_CMDecode.decode
def decode (x : Q) : K := ⟨dc x.c0,dc x.c1⟩

theorem zero : decode PV_OWNK_TowerCanon.zero = 0 := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl
theorem one : decode PV_OWNK_TowerCanon.one = 1 := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

theorem add (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueAdd x y) = decode x + decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_CMDecode.add _ _ hx.1 hy.1
 · exact PV_OWNK_CMDecode.add _ _ hx.2 hy.2

theorem sub (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueSub x y) = decode x - decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_CMDecode.sub _ _ hx.1 hy.1
 · exact PV_OWNK_CMDecode.sub _ _ hx.2 hy.2

theorem mul (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueMul x y) = decode x * decode y := by
 have hm0 := cm_mul x.c0 y.c0
 have hm1 := cm_mul x.c1 y.c1
 have hsx := cm_add x.c0 x.c1 hx.1 hx.2
 have hsy := cm_add y.c0 y.c1 hy.1 hy.2
 have hm2 := cm_mul (PV_B2_FieldValue.aspis_core.field.CM31.add x.c0 x.c1) (PV_B2_FieldValue.aspis_core.field.CM31.add y.c0 y.c1)
 apply QuadraticAlgebra.ext
 · change dc (PV_B2_FieldValue.aspis_core.field.CM31.add (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c0 y.c0)
    (PV_B2_FieldValue.aspis_core.field.mul_by_r (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c1 y.c1))) = _
   rw [PV_OWNK_CMDecode.add _ _ hm0 (mul_by_r _ hm1),
    PV_OWNK_CMDecode.mul_by_r _ hm1,
    PV_OWNK_CMDecode.mul _ _ hx.1 hy.1,PV_OWNK_CMDecode.mul _ _ hx.2 hy.2]
   rfl
 · change dc (PV_B2_FieldValue.aspis_core.field.CM31.sub (PV_B2_FieldValue.aspis_core.field.CM31.sub (PV_B2_FieldValue.aspis_core.field.CM31.mul (PV_B2_FieldValue.aspis_core.field.CM31.add x.c0 x.c1) (PV_B2_FieldValue.aspis_core.field.CM31.add y.c0 y.c1))
    (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c0 y.c0)) (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c1 y.c1)) = _
   rw [PV_OWNK_CMDecode.sub _ _ (cm_sub _ _ hm2 hm0) hm1,
    PV_OWNK_CMDecode.sub _ _ hm2 hm0,
    PV_OWNK_CMDecode.mul _ _ hsx hsy,
    PV_OWNK_CMDecode.add _ _ hx.1 hx.2,PV_OWNK_CMDecode.add _ _ hy.1 hy.2,
    PV_OWNK_CMDecode.mul _ _ hx.1 hy.1,PV_OWNK_CMDecode.mul _ _ hx.2 hy.2]
   simp only [decode,QuadraticAlgebra.im_mul]
   ring
#print axioms zero
#print axioms one
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.PV_OWNK_QMDecode
