import R1Z.PV_CB_Op110Source
import R1Z.ProverRwSuccessNativeNormalize
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_EmbeddingWord
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower

theorem reduce (x : U64) :
    PV_CB_ShippedOp110.aspis_core.field.ct.reduce64 x =
      ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64 x := by
  unfold PV_CB_ShippedOp110.aspis_core.field.ct.reduce64
    ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
    PV_CB_ShippedOp110.aspis_core.field.ct.subtract_p
    ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
    PV_CB_ShippedOp110.aspis_core.field.P
    ProverRwSuccessNativePorts.aspis_core.field.P AspisR1ProducerRelease47.field.P
  rfl

/-- Reuse the proved symbolic normalization transport for arbitrary raw words. -/
theorem canonical (q : aspis_core.field.QM31) :
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.canonical_qm31 q =
      ProverRwSuccessWideSource.normalize q := by
  refine Eq.trans ?_ (ProverRwSuccessNativeNormalize.transport q)
  simp only [PV_CB_ShippedOp110.aspis_core.field.wide_exact.canonical_qm31,
    ProverRwSuccessNativeNormalize.source,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31,
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    reduce]

theorem construct (q : aspis_core.field.QM31) :
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.from_qm31 q =
      mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 (toQ q)) := by
  simp only [PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.from_qm31,
    canonical,ProverRwSuccessWideSource.normalize,
    AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,fromW,fromQ,
    PV_CB_ShippedOp110.aspis_core.field.QM31.ZERO,
    AspisR1ProducerRelease47.field.QM31.ZERO,fromC]

#print axioms reduce
#print axioms canonical
#print axioms construct
end R1Z.PV_Join_EmbeddingWord
