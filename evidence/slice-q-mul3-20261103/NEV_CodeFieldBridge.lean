import NEV_CodeFieldRaw.Funs
import NBG_Embedding
import NBF_RowInstall
set_option autoImplicit false
noncomputable section
namespace NEV_CodeFieldBridge
open Aeneas Aeneas.Std Result
abbrev RawE := NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact
abbrev StageE := NBF_RowInstall.E

def value (x : U32) : RawE :=
  ⟨⟨⟨AspisS1M31Embedding.Total.reduce x,0#u32⟩,⟨0#u32,0#u32⟩⟩,
    ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

def toStage (x : RawE) : StageE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def fromStage (x : StageE) : RawE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem raw_roundtrip (x : RawE) : fromStage (toStage x)=x := by cases x;rfl

theorem stage_roundtrip (x : StageE) : toStage (fromStage x)=x := by cases x;rfl

/-- Reuse the existing generic remainder law; no arithmetic is reproved. -/
theorem rem (x : U32) : x % NEV_CodeFieldRaw.aspis_core.field.P =
    ok (AspisS1M31Embedding.Total.reduce x) := by
  simpa only [NEV_CodeFieldRaw.aspis_core.field.P,AspisS1M31Embedding.aspis_core.field.P]
    using AspisS1M31Embedding.Total.rem_total x

/-- Complete newly emitted frozen trait path on ALL raw words, including both
normalization passes. All reached definitions are emitted, not templates. -/
theorem total (x : U32) :
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
      ok (value x) := by
  simp only [NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.CM31.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.QM31.from_cm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    NEV_CodeFieldRaw.aspis_core.field.M31.ZERO,
    NEV_CodeFieldRaw.aspis_core.field.CM31.ZERO,
    NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO,
    rem,bind_tc_ok,AspisS1M31Embedding.Total.reduce_idempotent,
    AspisS1M31Embedding.Total.reduce_zero,value]

/-- This is the exact concrete callback installed in the adopted accumulation
cohort. Canonicality is required and must come from the caller's basis proof. -/
theorem cohort (ops : AspisR1.Port3_NativeQueryBody.Ops) (x : U32)
    (canonical : x.val<2147483647) :
    (do let out ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x
        ok (toStage out)) = (NBF_RowInstall.install ops).op10 x := by
  have reduced : AspisS1M31Embedding.Total.reduce x=x := by
    apply UScalar.eq_of_val_eq
    rw [AspisS1M31Embedding.Total.reduce_val]
    exact Nat.mod_eq_of_lt canonical
  rw [total,bind_tc_ok]
  simp only [toStage,value,reduced,NBF_RowInstall.install,NBF_RowInstall.embedM,NBF_RowInstall.zeroQ]

#print axioms raw_roundtrip
#print axioms stage_roundtrip
#print axioms rem
#print axioms total
#print axioms cohort
end NEV_CodeFieldBridge
end
