import CuSavingsRetainedSamplerPrepared
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSamplerInputs
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail CuSavingsRetainedSamplerBinding
variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]

theorem input_fromInput (value : I) : input (fromInput value)=value := rfl

theorem table_sources (N : Usize) (base : E)
    (hb : CuSavingsCanonicalDotsSources.SourceValue (input base))
    (source : Array I N) (hs : AspisR1CanonicalInputs.weights.powers N (input base)=.ok source)
    (i : Nat) (hi : i<N.val) :
    CuSavingsCanonicalDotsSources.SourceValue
      (input ((table source).val[i]'(by rw [(table source).property];exact hi))) := by
  have ho := CuSavingsCanonicalDotsSources.SourceValue.power N (input base) source i hi hb hs
  simpa only [table,List.getElem_map,input_fromInput] using ho

theorem twofold_inputs (common : PreparedCommon) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch finalScratch : Array E 29#usize) (out : verifier.Prepared)
    (h : letI : PreparedCommon := binding common
         gamma_new.Prepared.gamma_new_new D sem v hash scratch=.ok (.Ok out,finalScratch))
    (hf : transport.Variant.folds v.variant=.ok 2#usize) :
    (∃ a0 a1,out.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1)) ∧
    (∀ i (hi : i<29), CuSavingsCanonicalDotsSources.SourceValue
      (input (finalScratch.val[i]'(by rw [finalScratch.property];exact hi)))) := by
  obtain ⟨hg,_,a0,a1,ha,ha0,ha1,source,hpow,hfinal⟩ :=
    CuSavingsRetainedSamplerPrepared.source_success common D sem v hash scratch finalScratch out h
  have hsecond : CuSavingsLibraOrigins.Alpha (libra a1) := by
    cases ha1 with
    | inl h => exact h
    | inr h => exact False.elim (h.1 hf)
  refine ⟨⟨a0,a1,ha,ha0,hsecond⟩,?_⟩
  intro i hi
  subst finalScratch
  exact table_sources 29#usize out.gamma hg source hpow i hi

#print axioms input_fromInput
#print axioms table_sources
#print axioms twofold_inputs
end AspisR1.CuSavingsRetainedSamplerInputs
