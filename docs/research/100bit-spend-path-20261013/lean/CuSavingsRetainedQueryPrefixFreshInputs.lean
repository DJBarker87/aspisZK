import CuSavingsRetainedQueryPrefixFinish
import CuSavingsRetainedDotsInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixFreshInputs
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedQueryPrefixBinding
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
  [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]

theorem source_table {H : Type} (common : PreparedCommon)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (initial finalScratch : Array aspis_core.field.WideExact 29#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) (p : verifier.Prepared)
    (h : letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding common
         retained.tx1_prepare D pub v hash obs initial=.ok (.Ok (claims,p),finalScratch)) :
    SourceTable (CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide finalScratch) := by
  letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding common
  obtain ⟨sem,hprep⟩:=CuSavingsRetainedCompositionTx1.preparation_witness D pub v hash obs initial finalScratch claims p h
  obtain ⟨hg,_,a0,a1,_,_,_,source,hpow,hfinal⟩:=
    CuSavingsRetainedSamplerPrepared.source_success common D sem v hash initial finalScratch p hprep
  intro i hi
  have hs:=CuSavingsRetainedSamplerInputs.table_sources 29#usize p.gamma hg source hpow i hi
  subst finalScratch
  simpa only [CuSavingsRhoEntryTransport.array,List.getElem_map,
    CuSavingsRhoEntryTransport.wide,CuSavingsRhoEntryTransport.scalar,
    CuSavingsRetainedResumeDotBinding.input,CuSavingsRetainedSamplerBinding.input] using hs

#print axioms source_table
end AspisR1.CuSavingsRetainedQueryPrefixFreshInputs
