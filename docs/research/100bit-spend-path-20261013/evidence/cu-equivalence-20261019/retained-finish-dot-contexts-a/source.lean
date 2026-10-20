import CuSavingsRetainedFinishDotBinding
import CuSavingsRetainedFinishPrepared
import CuSavingsRetainedFinishResumed
set_option autoImplicit false
noncomputable section
namespace AspisR1.CuSavingsRetainedFinishDotContexts
open Aeneas Aeneas.Std Result
open CuSavingsRetainedFinishDotBinding CuSavingsRetainedFinishDotClients
namespace Prepared
open AspisR1RhoPowerTail
variable [AspisR1CanonicalDots.Shared]
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared] [AspisR1CuRho.ScalarKBlocks]
theorem source_equivalence {State : Type} (frame : Frames State) (base : CuSavingsRetainedFinishRelation.Boundaries State)
    (tx : AspisR1RhoTransactions.TxCommon) (common : PreparedCommon) (prefixCommon : RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize)
    (work : AspisR1RhoTransactions.verifier.Prepared → Array aspis_core.field.WideExact 29#usize →
      Result (core.result.Result AspisR1RhoTransactions.verifier.Accumulator AspisR1RhoTransactions.verifier.Error)) :
    CuSavingsRetainedFinishPrepared.run true (boundaries frame base newClients) tx common prefixCommon R B D pub v hash obs initial work=
    CuSavingsRetainedFinishPrepared.run false (boundaries frame base oldClients) tx common prefixCommon R B D pub v hash obs initial work := by
  rw [boundaries_equivalence frame base]
  exact CuSavingsRetainedFinishPrepared.source_equivalence (boundaries frame base oldClients) tx common prefixCommon R B D pub v hash obs initial work
#print axioms source_equivalence
end Prepared
namespace Resumed
open AspisR1RhoResumeCaller
variable [AspisR1CanonicalDots.Shared]
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
theorem source_equivalence {State : Type} (frame : Frames State) (base : CuSavingsRetainedFinishRelation.Boundaries State)
    (resume : CuSavingsRetainedResumeBinding.Boundaries) (common : AspisR1RhoTransactions.TxCommon)
    {H : Type} (D : aspis_core.Digest32 H) (bytes proof publicValue : Slice U8)
    (variant : transport.Variant) (hash : H) (v : AspisR1RhoTransactions.verifier.View)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase → Result Unit))
    (work : verifier.Prepared → verifier.Accumulator → Result (core.result.Result verifier.Accumulator verifier.Error)) :
    CuSavingsRetainedFinishResumed.run true (boundaries frame base newClients) resume common D bytes proof publicValue variant hash v obs work=
    CuSavingsRetainedFinishResumed.run false (boundaries frame base oldClients) resume common D bytes proof publicValue variant hash v obs work := by
  rw [boundaries_equivalence frame base]
  exact CuSavingsRetainedFinishResumed.source_equivalence (boundaries frame base oldClients) resume common D bytes proof publicValue variant hash v obs work
#print axioms source_equivalence
end Resumed
end AspisR1.CuSavingsRetainedFinishDotContexts
