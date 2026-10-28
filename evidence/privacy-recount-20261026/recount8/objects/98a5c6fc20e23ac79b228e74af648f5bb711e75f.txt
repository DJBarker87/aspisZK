import R1Z.ProverRwP6BodyStore
import R1Z.PV_Join_EmbeddingWord
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Embedding
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower

theorem quartic (x : U32) :
    PV_CB_ShippedOp110.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
      mapResult fromQ (ProverRwDictionaryScalar.qFrom x) := by
  simp only [PV_CB_ShippedOp110.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    ProverRwDictionaryScalar.qFrom,ProverRwDictionaryScalar.mFrom,
    PV_CB_ShippedOp110.aspis_core.field.P,AspisR1ProducerRelease47.field.P,
    PV_CB_ShippedOp110.aspis_core.field.CM31.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.QM31.from_cm31,
    PV_CB_ShippedOp110.aspis_core.field.M31.ZERO,
    AspisR1ProducerRelease47.field.CM31.from_m31,AspisR1ProducerRelease47.field.QM31.from_cm31,
    PV_CB_ShippedOp110.aspis_core.field.CM31.ZERO,
    AspisR1ProducerRelease47.field.CM31.ZERO,
    AspisR1ProducerRelease47.field.M31.ZERO,mapResult_bind,bind_assoc_eq,bind_tc_ok,fromQ,fromC]

theorem body (x : U32) :
    ProverRwDictionaryEmbedding.embed x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x := by
  unfold ProverRwDictionaryEmbedding.embed
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
  rw [quartic]
  simp only [mapResult_bind,bind_assoc_eq,bind_tc_ok,PV_Join_EmbeddingWord.construct,native_q_roundtrip]

variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op110 x = (PV_CB_Op110Source.selected ops).op110 x := body x
theorem op110_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op110 x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x :=
  (selected_bridge ops x).trans (PV_CB_Op110Source.op110_source ops x)
#print axioms quartic
#print axioms body
#print axioms selected_bridge
#print axioms op110_source
end R1Z.PV_Join_Embedding
