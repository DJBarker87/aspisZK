import R1Z.ProverRwP6BodyData
import R1Z.PV_Join_EmbeddingWord
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Embedding
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower

/-- from_m31 first takes a remainder; only that canonical word and three zero
words reach canonical_qm31. No unrestricted normalization equality is assumed. -/
theorem body (x : U32) :
    ProverRwDictionaryEmbedding.embed x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x := by
  obtain ⟨word,hr,hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y := AspisR1ProducerRelease47.field.P)
      (by rw [AspisR1ProducerRelease47.field.P]; decide))
  have bound : word.val < 2147483647 := by
    rw [hval]
    exact Nat.mod_lt _ (by decide)
  have hr' : x % PV_CB_ShippedOp110.aspis_core.field.P = ok word := by
    simpa only [PV_CB_ShippedOp110.aspis_core.field.P,AspisR1ProducerRelease47.field.P] using hr
  simp only [ProverRwDictionaryEmbedding.embed,ProverRwDictionaryScalar.qFrom,
    ProverRwDictionaryScalar.mFrom,hr,bind_tc_ok,
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    hr',PV_CB_ShippedOp110.aspis_core.field.CM31.from_m31,
    PV_CB_ShippedOp110.aspis_core.field.QM31.from_cm31,
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.from_qm31,
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.canonical_qm31,
    PV_CB_ShippedOp110.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    PV_CB_ShippedOp110.aspis_core.field.M31.ZERO,
    PV_CB_ShippedOp110.aspis_core.field.QM31.ZERO,
    PV_Join_EmbeddingWord.current word bound,PV_Join_EmbeddingWord.current 0#u32 (by decide),
    AspisR1ProducerRelease47.field.CM31.from_m31,AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1ProducerRelease47.field.M31.ZERO,AspisR1ProducerRelease47.field.CM31.ZERO,
    AspisR1ProducerRelease47.field.QM31.ZERO,mapResult,fromW,fromQ,fromC]
  have self : word % AspisR1ProducerRelease47.field.P = ok word := by
    obtain ⟨r,run,value⟩ := WP.spec_imp_exists
      (UScalar.rem_spec word (y := AspisR1ProducerRelease47.field.P)
        (by rw [AspisR1ProducerRelease47.field.P]; decide))
    have same : r = word := by
      apply UScalar.eq_of_val_eq
      rw [value]
      exact Nat.mod_eq_of_lt bound
    simpa only [same] using run
  rw [self]
  rfl
variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op110 x = (PV_CB_Op110Source.selected ops).op110 x := body x
theorem op110_source (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (ProverRwP6BodyStore.selected ops).op110 x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x :=
  (selected_bridge ops x).trans (PV_CB_Op110Source.op110_source ops x)
#print axioms body
#print axioms selected_bridge
#print axioms op110_source
end R1Z.PV_Join_Embedding
