import S1M31EmbeddingTotalV1
set_option autoImplicit false
noncomputable section
namespace NBG_Embedding
open Aeneas Aeneas.Std Result AspisS1M31Embedding

/-- Inventory correction: the coherent closure already contains this exact
trait member in S1M31EmbeddingSourceV1; it was missed by NBI2's name scan. -/
theorem from_m31_result (x : U32) :
    aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
      ok (AspisS1M31Embedding.Total.value x) :=
  AspisS1M31Embedding.Total.source_total x

/-- All raw QM31 limbs are normalized, and all four upper limbs are zero. -/
theorem from_qm31_result (x : aspis_core.field.QM31) :
    aspis_core.field.wide_exact.WideExact.from_qm31 x =
      ok (⟨⟨⟨Total.reduce x.c0.a,Total.reduce x.c0.b⟩,
          ⟨Total.reduce x.c1.a,Total.reduce x.c1.b⟩⟩,
        ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩ : aspis_core.field.wide_exact.WideExact) := by
  simp only [aspis_core.field.wide_exact.WideExact.from_qm31,
    aspis_core.field.wide_exact.canonical_qm31,
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    Total.rem_total,bind_tc_ok,aspis_core.field.QM31.ZERO]

#print axioms from_m31_result
#print axioms from_qm31_result
#print axioms AspisS1M31Embedding.Total.reduce_val
end NBG_Embedding
