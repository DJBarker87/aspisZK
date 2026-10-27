import RPz7_SAF_ReducedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIs_Pair
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
def Law {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact) : Prop := ∀ (weights : W) (alphas : Slice E) (value : E),
    ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas →
    ops.pair weights alphas v.final_message p.kappa = ok (.Ok value) →
    CheckpointBytes5Output.ofE value = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa)))

end AspisR1.FIs_Pair
end
