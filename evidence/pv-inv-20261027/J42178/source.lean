import R1Z.PV_Inv_EmbedTag
import R1Z.PV_Inv_CompressionFinite
import R0P.Copy
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_CompressTuple
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitNativeQ48 (source)

theorem compress_exact (lambda : Old.Q) (hl : Canonical lambda) (tag : U32)
    (htag : tag.val < AspisCircleGroupOrder.P) (limbs : Fin 16 → U32) :
    ∃ z : Old.Q,
      PV_Inv_NativeCompress.loop (source lambda) (source (PV_Inv_EmbedTag.liftWord tag))
        (source lambda) (List.ofFn limbs)=ok (source z) ∧ Canonical z ∧
      decode z=R0P.copyTupleValue (decode lambda)
        (ProverCommitScalar48.embed tag,fun i => ProverCommitScalar48.embed (limbs i)) := by
  obtain ⟨z,hz,hc,hv⟩ := PV_Inv_NativeCompress.exact_value lambda (PV_Inv_EmbedTag.liftWord tag)
    lambda (List.ofFn limbs) hl (PV_Inv_EmbedTag.canonical tag htag) hl
  refine ⟨z,hz,hc,?_⟩
  rw [hv,PV_Inv_EmbedTag.value,List.map_ofFn,PV_Inv_CompressionFinite.tagged_sixteen]
  rfl

#print axioms compress_exact
end R1Z.PV_Inv_CompressTuple
