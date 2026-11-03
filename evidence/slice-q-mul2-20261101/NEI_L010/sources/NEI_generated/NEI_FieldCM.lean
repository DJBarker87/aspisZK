import NEI_FieldScalar
set_option autoImplicit false
noncomputable section
namespace NEI_FieldCM
open Aeneas Aeneas.Std Result NEI_FieldCarriers NEI_FieldScalar
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem cm_add (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.add x y) =
      AspisR1CurrentWide.field.CM31.add (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.add,
    AspisR1CurrentWide.field.CM31.add, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_sub (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.sub x y) =
      AspisR1CurrentWide.field.CM31.sub (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.sub,
    AspisR1CurrentWide.field.CM31.sub, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_mul (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.mul x y) =
      AspisR1CurrentWide.field.CM31.mul (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.mul,
    AspisR1CurrentWide.field.CM31.mul, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_mul_m31 (x : N.C) (y : U32) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.mul_m31 x y) =
      AspisR1CurrentWide.field.CM31.mul_m31 (toC x) y := by
  simp only [NEI_LineFull.aspis_core.field.CM31.mul_m31,
    AspisR1CurrentWide.field.CM31.mul_m31, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem by_r (x : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.mul_by_r x) =
      AspisR1CurrentWide.field.mul_by_r (toC x) := by
  simp only [NEI_LineFull.aspis_core.field.mul_by_r,
    AspisR1CurrentWide.field.mul_by_r, resultMap_bind,
    m_double,m_add,m_sub,okC,toC]

#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms cm_mul_m31
#print axioms by_r
end NEI_FieldCM
end
