import LIB_VCarriers
import NGM_LPi_TowerValues
set_option autoImplicit false
noncomputable section
namespace LIB_VArithmetic
open Aeneas Aeneas.Std LIB_VScalarCarriers
/-- Canonicality is carried by the input type, never a caller success premise. -/
theorem add_total (x y : QM31) :
 ∃ z : NQ, canonQ z ∧ FIo_Native.aspis_core.field.QM31.add x.val y.val = .ok z := by
 obtain ⟨z,run,cz,_⟩ := AspisR1.LPi_TowerValues.qm_add x.val y.val x.property y.property
 exact ⟨z,cz,run⟩
theorem mul_total (x y : QM31) :
 ∃ z : NQ, canonQ z ∧ FIo_Native.aspis_core.field.QM31.mul x.val y.val = .ok z := by
 obtain ⟨z,run,cz,_⟩ := AspisR1.LPi_TowerValues.qm_mul x.val y.val x.property y.property
 exact ⟨z,cz,run⟩
def qadd (x y : QM31) : QM31 :=
 ⟨Classical.choose (add_total x y),(Classical.choose_spec (add_total x y)).1⟩
def qmul (x y : QM31) : QM31 :=
 ⟨Classical.choose (mul_total x y),(Classical.choose_spec (mul_total x y)).1⟩
theorem qadd_native (x y : QM31) :
 FIo_Native.aspis_core.field.QM31.add x.val y.val = .ok (qadd x y).val :=
 (Classical.choose_spec (add_total x y)).2
theorem qmul_native (x y : QM31) :
 FIo_Native.aspis_core.field.QM31.mul x.val y.val = .ok (qmul x y).val :=
 (Classical.choose_spec (mul_total x y)).2
#print axioms add_total
#print axioms mul_total
#print axioms qadd_native
#print axioms qmul_native
end LIB_VArithmetic
