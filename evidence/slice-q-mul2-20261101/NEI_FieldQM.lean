import NEI_FieldCM
set_option autoImplicit false
noncomputable section
namespace NEI_FieldQM
open Aeneas Aeneas.Std Result NEI_FieldCarriers NEI_FieldCM
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem qm_add (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.add x y) =
      AspisR1CurrentWide.field.QM31.add (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.add,
    AspisR1CurrentWide.field.QM31.add,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_sub (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.sub x y) =
      AspisR1CurrentWide.field.QM31.sub (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.sub,
    AspisR1CurrentWide.field.QM31.sub,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_mul (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.mul,
    AspisR1CurrentWide.field.QM31.mul,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_mul_m31 (x : N.Q) (y : U32) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.mul_m31 x y) =
      AspisR1CurrentWide.field.QM31.mul_m31 (toQ x) y := by
  simp only [NEI_LineFull.aspis_core.field.QM31.mul_m31,
    AspisR1CurrentWide.field.QM31.mul_m31,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem mul_u (x : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.wide_exact.mul_u x) =
      AspisR1CurrentWide.field.wide_exact.mul_u (toQ x) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.mul_u,
    AspisR1CurrentWide.field.wide_exact.mul_u,bindC,by_r,okQ,toQ,tofromC] <;> rfl

#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms qm_mul_m31
#print axioms mul_u
end NEI_FieldQM
end
