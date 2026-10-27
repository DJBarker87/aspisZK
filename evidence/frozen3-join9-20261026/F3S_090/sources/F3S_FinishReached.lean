import F3S_RoundValues
import F3R_FinishSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FinishReached
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Port4D_Round.round
 theorem reached {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (s2 : p.variant=.S2)
    (success : Port4D_FinishInstall.finish ops v p a none=ok (.Ok ())) :
    ∃ (alpha0 alpha1 value0 value1 : E) (weights : W) (alphas : Slice E) (pair dot : E),
      Array.index_usize p.alpha 0#usize=ok alpha0 ∧
      Array.index_usize p.alpha 1#usize=ok alpha1 ∧
      Port4D_Round.round (Port3_FinishStage.release ops) v.round0 alpha0 p.claim 0#usize=ok (.Ok value0) ∧
      Port4D_Round.round (Port3_FinishStage.release ops) v.round1 alpha1 value0 1#usize=ok (.Ok value1) ∧
      ops.newWeights p.variant p.semantic_alpha p.z=ok (.Ok weights) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alphas ∧
      ops.pair weights alphas v.final_message p.kappa=ok (.Ok pair) ∧
      ops.dot v.final_message a.weights.deref=ok (.Ok dot) := by
  have source := F3R_FinishSource.accepted ops v p a success
  unfold Port3_NativeFinishBody.verifier.finish_relation Port4D_Round.native Port3_FinishStage.native at source
  simp only [Port3_FinishStage.release,Port3_FinishStage.folds,s2,lift,bind_tc_ok] at source ⊢
  repeat' first
    | (solve | cases source)
    | uncase_result
    | head_reduce source
    | split at source
  all_goals refine ⟨_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,by assumption⟩
#print axioms reached
end AspisR1.F3S_FinishReached
end
