import CuSavingsRetainedCompositionTx1
import CuSavingsRetainedSamplerInputs
import CuSavingsRetainedSamplerSemanticCopy
import CuSavingsRetainedSemanticInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedPreparationInputs
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]

theorem preparation_inputs (common : PreparedCommon) (prefixCommon : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (d : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (initial finalScratch : Array aspis_core.field.WideExact 29#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) (out : verifier.Prepared)
    (h : letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
         letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefixCommon R B
         retained.tx1_prepare d pub v hash obs initial=.ok (.Ok (claims,out),finalScratch))
    (hf : transport.Variant.folds v.variant=.ok 2#usize) :
    (∃ a0 a1,out.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedSamplerBinding.libra a0) ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedSamplerBinding.libra a1)) ∧
    (∀ i (hi : i<29),CuSavingsCanonicalDotsSources.SourceValue
      (CuSavingsRetainedSamplerBinding.input
        (finalScratch.val[i]'(by rw [finalScratch.property];exact hi)))) ∧
    (∀ i : Fin 10,CuSavingsLibraConcrete.canonicalK
      (CuSavingsRetainedSemanticBinding.libraK
        (out.semantic_alpha.val[i.val]'(by rw [out.semantic_alpha.property];exact i.isLt)))) := by
  letI : PreparedCommon := CuSavingsRetainedSamplerBinding.binding common
  letI : RetainedPrefix := CuSavingsRetainedSemanticBinding.binding prefixCommon R B
  obtain ⟨sem,hs,hp⟩ := CuSavingsRetainedCompositionTx1.preparation_origins
    d pub v hash obs initial finalScratch claims out h
  have hc := CuSavingsRetainedSemanticInputs.verify_alpha_canonical R B d pub v.semantic hash obs sem hs
  have hcopy := CuSavingsRetainedSamplerSemanticCopy.source_success d sem v hash initial finalScratch out hp
  obtain ⟨halpha,hgamma⟩ := CuSavingsRetainedSamplerInputs.twofold_inputs
    common d sem v hash initial finalScratch out hp hf
  refine ⟨halpha,hgamma,?_⟩
  intro i
  simpa only [hcopy] using hc i

#print axioms preparation_inputs
end AspisR1.CuSavingsRetainedPreparationInputs
