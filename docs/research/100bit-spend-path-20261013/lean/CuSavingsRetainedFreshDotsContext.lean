import CuSavingsRetainedDotsInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFreshDotsContext
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedDotsInputs
abbrev Claims := Array (Array aspis_core.field.QM31 29#usize) 3#usize
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
  [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]

def run {H O : Type} (common : PreparedCommon) (dot : AspisR1RetainedDots.Shared)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (scratch : Array P 29#usize) (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (onError : verifier.Error→Array P 29#usize→Result O)
    (ctx : Claims→verifier.Prepared→Array P 29#usize→Slice U8→
      (Unit→Result (Array CuSavingsRetainedDotsBinding.E 4#usize))→Result O)
    (kernel : AspisR1RetainedDots.Shared→Slice U8→CuSavingsRetainedDotsTail.G→
      Result (Array CuSavingsRetainedDotsBinding.E 4#usize)) : Result O :=
  letI : PreparedCommon:=CuSavingsRetainedSamplerBinding.binding common
  do
  let (result,finalScratch)←retained.tx1_prepare D pub v hash obs scratch
  match result with
  | .Err error=>onError error finalScratch
  | .Ok (claims,p)=>
    let bytes←AspisR1CuQuery.verifier.View.query view index
    ctx claims p finalScratch bytes (fun _=>kernel dot bytes (gamma finalScratch))

theorem source_equivalence {H O : Type} (common : PreparedCommon) (dot : AspisR1RetainedDots.Shared)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (scratch : Array P 29#usize) (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (onError : verifier.Error→Array P 29#usize→Result O)
    (ctx : Claims→verifier.Prepared→Array P 29#usize→Slice U8→
      (Unit→Result (Array CuSavingsRetainedDotsBinding.E 4#usize))→Result O) :
    run common (CuSavingsRetainedDotsBinding.newShared dot) D pub v hash obs scratch view index onError ctx
      (@AspisR1RetainedDots.prefix_new_dots.four_dots) =
    run common (CuSavingsRetainedDotsBinding.oldShared dot) D pub v hash obs scratch view index onError ctx
      (@AspisR1RetainedDots.old_dots.four_dots) := by
  unfold run
  apply (bind_eq_iff _ _ _).mpr
  intro pair hprepare
  rcases pair with ⟨result,finalScratch⟩
  simp only [uncurry_apply_pair]
  cases result with
  | Err error=>rfl
  | Ok pair=>
    rcases pair with ⟨claims,p⟩
    exact fresh_source_equivalence common dot D pub v hash obs scratch finalScratch claims p
      hprepare view index (ctx claims p finalScratch)

#print axioms source_equivalence
end AspisR1.CuSavingsRetainedFreshDotsContext
