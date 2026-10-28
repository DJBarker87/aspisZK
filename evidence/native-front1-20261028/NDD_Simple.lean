import NDD_Reference.Funs
import AspisR72Sampler.Funs
import S1M31EmbeddingSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Simple
theorem m31_neg (x : U32) :
    NDD_Reference.m31_neg_ref x = AspisR72Sampler.field.M31.neg x := by
  simp only [NDD_Reference.m31_neg_ref, AspisR72Sampler.field.M31.neg,
    AspisR72Sampler.field.P]
  split
  · rfl
  · cases (2147483647#u32 - x : Result U32) <;> rfl

theorem cm31_from (x : U32) :
    NDD_Reference.cm31_from_ref x = (do
      let c ← AspisS1M31Embedding.aspis_core.field.CM31.from_m31 x
      ok (Array.make 2#usize [c.a, c.b])) := by
  simp only [NDD_Reference.cm31_from_ref,
    AspisS1M31Embedding.aspis_core.field.CM31.from_m31,
    AspisS1M31Embedding.aspis_core.field.M31.ZERO]
  rfl
#print axioms m31_neg
#print axioms cm31_from
end NDD_Simple
