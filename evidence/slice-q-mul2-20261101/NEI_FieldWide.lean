import NEI_FieldQM
set_option autoImplicit false
noncomputable section
namespace NEI_FieldWide
open Aeneas Aeneas.Std Result NEI_FieldCarriers NEI_FieldQM
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem wide_add (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.add x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.add,
    AspisR1CurrentWide.field.wide_exact.WideExact.add,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_sub (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.sub x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.sub (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.sub,
    AspisR1CurrentWide.field.wide_exact.WideExact.sub,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_mul (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul,
    AspisR1CurrentWide.field.wide_exact.WideExact.mul,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_mul_m31 (x : N.E) (y : U32) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul_m31 x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) y := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul_m31,
    AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

#print axioms wide_add
#print axioms wide_sub
#print axioms wide_mul
#print axioms wide_mul_m31
end NEI_FieldWide
end
