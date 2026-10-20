import CuSavingsRetainedResumeWhole
import CuSavingsRetainedResumeDotBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeDotsContext
open Aeneas Aeneas.Std Result
open CuSavingsRetainedResumeDotBinding
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]

def run {H O : Type} (tx : AspisR1RhoTransactions.TxCommon)
    (B : CuSavingsRetainedResumeBinding.Boundaries)
    (dot : AspisR1RetainedDots.Shared)
    (digest : AspisR1RhoResumeCaller.aspis_core.Digest32 H)
    (bytes proof public1 : Slice U8) (variant : AspisR1RhoResumeCaller.transport.Variant) (hash : H)
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (onError : AspisR1RhoResumeCaller.verifier.Error→Result O)
    (ctx : AspisR1RhoResumeCaller.verifier.Prepared→AspisR1RhoResumeCaller.verifier.Accumulator→
      Array Q 29#usize→(Unit→Result (Array CuSavingsRetainedDotsBinding.E 4#usize))→Result O)
    (kernel : AspisR1RetainedDots.Shared→Slice U8→CuSavingsRetainedDotsTail.G→
      Result (Array CuSavingsRetainedDotsBinding.E 4#usize)) : Result O := do
  let result←@AspisR1RhoResumeCaller.source_resume_caller (CuSavingsRetainedResumeBinding.binding B)
    H digest bytes proof public1 variant hash
  match result with
  | .Err error=>onError error
  | .Ok (p,a)=>
    let powers←@(AspisR1RhoTransactions.weights.powers) (binding tx) 29#usize p.gamma
    let queryBytes←AspisR1CuQuery.verifier.View.query view index
    ctx p a powers (fun _=>kernel dot queryBytes (CuSavingsRetainedDotsInputs.gamma (preparedTable powers)))

theorem source_equivalence {H O : Type} (tx : AspisR1RhoTransactions.TxCommon)
    (B : CuSavingsRetainedResumeBinding.Boundaries) (dot : AspisR1RetainedDots.Shared)
    (digest : AspisR1RhoResumeCaller.aspis_core.Digest32 H)
    (bytes proof public1 : Slice U8) (variant : AspisR1RhoResumeCaller.transport.Variant) (hash : H)
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (onError : AspisR1RhoResumeCaller.verifier.Error→Result O)
    (ctx : AspisR1RhoResumeCaller.verifier.Prepared→AspisR1RhoResumeCaller.verifier.Accumulator→
      Array Q 29#usize→(Unit→Result (Array CuSavingsRetainedDotsBinding.E 4#usize))→Result O) :
    run tx B (CuSavingsRetainedDotsBinding.newShared dot) digest bytes proof public1 variant hash
      view index onError ctx (@AspisR1RetainedDots.prefix_new_dots.four_dots) =
    run tx B (CuSavingsRetainedDotsBinding.oldShared dot) digest bytes proof public1 variant hash
      view index onError ctx (@AspisR1RetainedDots.old_dots.four_dots) := by
  unfold run
  apply (bind_eq_iff _ _ _).mpr
  intro result hresume
  cases result with
  | Err error=>rfl
  | Ok pair=>
    rcases pair with ⟨p,a⟩
    have origin := (CuSavingsRetainedResumeWhole.source_inputs B digest bytes proof public1 variant hash p a hresume).1
    apply (bind_eq_iff _ _ _).mpr
    intro powers hpower
    exact query_equivalence tx dot p.gamma origin powers hpower view index (ctx p a powers)

#print axioms source_equivalence
end AspisR1.CuSavingsRetainedResumeDotsContext
