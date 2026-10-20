import CuSavingsRetainedDotsKernel
import CuSavingsRetainedSamplerInputs
import CuSavingsRetainedCompositionTx1
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsInputs
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsRetainedDotsBinding CuSavingsRetainedDotsTail
abbrev P := AspisR1RhoPowerTail.aspis_core.field.WideExact

def fromPrepared (x : P) : E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def gamma (xs : Array P 29#usize) : G :=
  ⟨xs.val.map fromPrepared,by simp only [List.length_map,xs.property]⟩

variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]

theorem source_gamma (values : Array P 29#usize)
    (hs : ∀ i (hi : i<29),CuSavingsCanonicalDotsSources.SourceValue
      (CuSavingsRetainedSamplerBinding.input (values.val[i]'(by rw [values.property];exact hi)))) :
    CanonicalG (gamma values) := by
  intro index value hread
  by_cases hi : index.val<(gamma values).val.length
  · have hr : Array.index_usize (gamma values) index=.ok ((gamma values).val[index.val]'hi) := by
      unfold Array.index_usize
      simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]
    rw [hr] at hread
    cases Result.ok.inj hread
    have h29 : (29#usize).val=29 := by scalar_tac
    have hi29 : index.val<29 := by simpa only [(gamma values).property,h29] using hi
    have hc := CuSavingsCanonicalDotsSources.input_canonical _
      (CuSavingsCanonicalDotsSources.source_canonical _ (hs index.val hi29))
    simpa only [gamma,List.getElem_map,fromPrepared,toE,toK,CuSavingsCanonicalDotsSources.inputToDot,CuSavingsRetainedSamplerBinding.input] using hc
  · unfold Array.index_usize at hread
    have hn : (gamma values).val[index.val]?=none := List.getElem?_eq_none (by omega)
    simp only [Array.getElem?_Usize_eq,hn] at hread
    cases hread

theorem query_equivalence {O : Type} (common : Shared)
    (view : AspisR1CuQuery.verifier.View) (index : Usize) (values : Array P 29#usize)
    (hs : ∀ i (hi : i<29),CuSavingsCanonicalDotsSources.SourceValue
      (CuSavingsRetainedSamplerBinding.input (values.val[i]'(by rw [values.property];exact hi))))
    (ctx : Slice U8→(Unit→Result (Array E 4#usize))→Result O) :
    (do let bytes←AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>@prefix_new_dots.four_dots (newShared common) bytes (gamma values))) =
      (do let bytes←AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>@old_dots.four_dots (oldShared common) bytes (gamma values))) := by
  apply (bind_eq_iff _ _ _).mpr
  intro bytes hquery
  apply congrArg (ctx bytes)
  funext unit
  exact CuSavingsRetainedDotsKernel.combined_eq common bytes
    (CuSavingsQueryAccess.query_prefix_bound view index bytes hquery) (gamma values) (source_gamma values hs)

variable [AspisR1CuRho.ScalarKBlocks] [AspisR1RhoPowerTail.RetainedPrefix]
theorem fresh_source_equivalence {H O : Type}
    (preparedCommon : AspisR1RhoPowerTail.PreparedCommon) (dotCommon : Shared)
    (D : AspisR1RhoPowerTail.aspis_core.Digest32 H)
    (pub : AspisR1RhoPowerTail.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : AspisR1RhoPowerTail.verifier.View) (hash : H)
    (obs : Option (AspisR1RhoPowerTail.verifier.Phase→Result Unit))
    (initial finalScratch : Array P 29#usize)
    (claims : Array (Array AspisR1RhoPowerTail.aspis_core.field.QM31 29#usize) 3#usize)
    (p : AspisR1RhoPowerTail.verifier.Prepared)
    (hp : letI : AspisR1RhoPowerTail.PreparedCommon := CuSavingsRetainedSamplerBinding.binding preparedCommon
          AspisR1RhoPowerTail.retained.tx1_prepare D pub v hash obs initial=.ok (.Ok (claims,p),finalScratch))
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (ctx : Slice U8→(Unit→Result (Array E 4#usize))→Result O) :
    (do let bytes←AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>@prefix_new_dots.four_dots (newShared dotCommon) bytes (gamma finalScratch))) =
      (do let bytes←AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>@old_dots.four_dots (oldShared dotCommon) bytes (gamma finalScratch))) := by
  letI : AspisR1RhoPowerTail.PreparedCommon := CuSavingsRetainedSamplerBinding.binding preparedCommon
  obtain ⟨sem,hprep⟩ := CuSavingsRetainedCompositionTx1.preparation_witness
    D pub v hash obs initial finalScratch claims p hp
  obtain ⟨hg,_,a0,a1,_,_,_,source,hpow,hfinal⟩ :=
    CuSavingsRetainedSamplerPrepared.source_success preparedCommon D sem v hash initial finalScratch p hprep
  apply query_equivalence dotCommon view index finalScratch ?_ ctx
  intro i hi
  subst finalScratch
  exact CuSavingsRetainedSamplerInputs.table_sources 29#usize p.gamma hg source hpow i hi

#print axioms source_gamma
#print axioms query_equivalence
#print axioms fresh_source_equivalence
end AspisR1.CuSavingsRetainedDotsInputs
