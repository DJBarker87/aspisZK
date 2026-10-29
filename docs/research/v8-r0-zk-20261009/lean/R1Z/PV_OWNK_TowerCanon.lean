import R1Z.PV_OWNK_ScalarOps
set_option autoImplicit false
namespace R1Z.PV_OWNK_TowerCanon
open Aeneas Aeneas.Std
open PV_OWNI_RawOps
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev CM := PV_B2_FieldValue.aspis_core.field.CM31
abbrev QM := PV_B2_FieldValue.aspis_core.field.QM31
def CC (x : C) : Prop := PV_OWNK_ScalarOps.Canon x.a ∧ PV_OWNK_ScalarOps.Canon x.b
def Canon (x : Q) : Prop := CC x.c0 ∧ CC x.c1

theorem cm_add (x y : C) (hx : CC x) (hy : CC y) : CC (CM.add x y) :=
 ⟨PV_OWNK_ScalarOps.add_canon _ _ hx.1 hy.1,PV_OWNK_ScalarOps.add_canon _ _ hx.2 hy.2⟩
theorem cm_sub (x y : C) (hx : CC x) (hy : CC y) : CC (CM.sub x y) :=
 ⟨PV_OWNK_ScalarOps.sub_canon _ _ hx.1 hy.1,PV_OWNK_ScalarOps.sub_canon _ _ hx.2 hy.2⟩
/-- The three partial products are reduced even for arbitrary raw inputs. -/
theorem cm_mul (x y : C) : CC (CM.mul x y) := by
 change PV_OWNK_ScalarOps.Canon _ ∧ PV_OWNK_ScalarOps.Canon _
 constructor
 · exact PV_OWNK_ScalarOps.sub_canon _ _
    (PV_OWNK_ScalarOps.mul_canon _ _) (PV_OWNK_ScalarOps.mul_canon _ _)
 · exact PV_OWNK_ScalarOps.sub_canon _ _
    (PV_OWNK_ScalarOps.sub_canon _ _ (PV_OWNK_ScalarOps.reduce_canon _)
     (PV_OWNK_ScalarOps.mul_canon _ _)) (PV_OWNK_ScalarOps.mul_canon _ _)

theorem mul_by_r (x : C) (hx : CC x) :
 CC (PV_B2_FieldValue.aspis_core.field.mul_by_r x) :=
 ⟨PV_OWNK_ScalarOps.sub_canon _ _ (PV_OWNK_ScalarOps.double_canon _ hx.1) hx.2,
  PV_OWNK_ScalarOps.add_canon _ _ hx.1 (PV_OWNK_ScalarOps.double_canon _ hx.2)⟩
theorem zero_canon : Canon zero := by
 constructor <;> constructor <;> change 0 < 2147483647 <;> omega
theorem one_canon : Canon one := by
 constructor
 · exact ⟨by change 1 < 2147483647; omega,by change 0 < 2147483647; omega⟩
 · constructor <;> change 0 < 2147483647 <;> omega
theorem qm_add (x y : Q) (hx : Canon x) (hy : Canon y) : Canon (valueAdd x y) :=
 ⟨cm_add _ _ hx.1 hy.1,cm_add _ _ hx.2 hy.2⟩
theorem qm_sub (x y : Q) (hx : Canon x) (hy : Canon y) : Canon (valueSub x y) :=
 ⟨cm_sub _ _ hx.1 hy.1,cm_sub _ _ hx.2 hy.2⟩
theorem qm_mul (x y : Q) : Canon (valueMul x y) :=
 ⟨cm_add _ _ (cm_mul _ _) (mul_by_r _ (cm_mul _ _)),
  cm_sub _ _ (cm_sub _ _ (cm_mul _ _) (cm_mul _ _)) (cm_mul _ _)⟩
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms mul_by_r
#print axioms zero_canon
#print axioms one_canon
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
end R1Z.PV_OWNK_TowerCanon
