import CuSavingsRetainedFinishBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFinishResumed
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]
/-- The exact complete resume returns its immutable Prepared. The unchanged
transaction stage updates only the Accumulator; on success the actual
TxCommon.finishRelation field is invoked unconditionally. -/
def run {State : Type} (newer : Bool) (B : CuSavingsRetainedFinishRelation.Boundaries State)
    (resume : CuSavingsRetainedResumeBinding.Boundaries) (common : AspisR1RhoTransactions.TxCommon)
    {H : Type} (D : aspis_core.Digest32 H) (bytes proof publicValue : Slice U8)
    (variant : transport.Variant) (hash : H) (v : AspisR1RhoTransactions.verifier.View)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase → Result Unit))
    (work : verifier.Prepared → verifier.Accumulator → Result (core.result.Result verifier.Accumulator verifier.Error)) :
    Result (core.result.Result Unit verifier.Error) :=
  letI : ResumeCommon := CuSavingsRetainedResumeBinding.binding resume
  letI : AspisR1RhoTransactions.TxCommon := CuSavingsRetainedFinishBinding.binding newer B common
  CuSavingsRetainedFinishBinding.sourceTry (source_resume_caller D bytes proof publicValue variant hash) fun (p,a) =>
    CuSavingsRetainedFinishBinding.sourceTry (work p a) fun updated =>
      AspisR1RhoTransactions.finish_relation v p updated obs

theorem source_equivalence {State : Type} (B : CuSavingsRetainedFinishRelation.Boundaries State)
    (resume : CuSavingsRetainedResumeBinding.Boundaries) (common : AspisR1RhoTransactions.TxCommon)
    {H : Type} (D : aspis_core.Digest32 H) (bytes proof publicValue : Slice U8)
    (variant : transport.Variant) (hash : H) (v : AspisR1RhoTransactions.verifier.View)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase → Result Unit))
    (work : verifier.Prepared → verifier.Accumulator → Result (core.result.Result verifier.Accumulator verifier.Error)) :
    run true B resume common D bytes proof publicValue variant hash v obs work=
    run false B resume common D bytes proof publicValue variant hash v obs work := by
  letI : ResumeCommon := CuSavingsRetainedResumeBinding.binding resume
  unfold run CuSavingsRetainedFinishBinding.sourceTry
  apply (bind_eq_iff (source_resume_caller D bytes proof publicValue variant hash) _ _).mpr
  intro result hr
  cases result with
  | Err error => rfl
  | Ok pair =>
    rcases pair with ⟨p,a⟩
    simp only [uncurry_apply_pair]
    obtain ⟨_,ha,hc⟩ := CuSavingsRetainedResumeWhole.source_inputs resume D bytes proof publicValue variant hash p a hr
    apply (bind_eq_iff (work p a) _ _).mpr
    intro result hw
    cases result with
    | Err error => rfl
    | Ok updated => exact CuSavingsRetainedFinishBinding.source_equivalence B v p updated obs ha hc

#print axioms source_equivalence
end AspisR1.CuSavingsRetainedFinishResumed
