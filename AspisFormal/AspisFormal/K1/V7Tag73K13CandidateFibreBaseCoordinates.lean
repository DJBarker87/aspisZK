import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting

/-!
# Base-coordinate equality for candidate-directed K1.3

The candidate-directed regrouping fixes the residual, alpha and q16-forest
context plus the separately exposed fold and final-work values.  Those five
equalities reconstruct the entire left/pre-answer side of the underlying
542-coordinate product.  This leaf is deliberately independent of the large
source-witness hierarchy.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CandidateFibreBaseCoordinates

open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

/-- The exact context/fold/work fibre determines every coordinate preceding
the query-batch duplex. -/
theorem candidate_context_fold_work_eq_implies_base_coordinates_eq
    {parameters : ExactCompilerResourceParameters}
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (contextExact :
      let leftRaw :=
        exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
          router left
      let rightRaw :=
        exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
          router right
      (leftRaw.1.1, (leftRaw.1.2.2.1, leftRaw.1.2.2.2.2)) =
        (rightRaw.1.1, (rightRaw.1.2.2.1, rightRaw.1.2.2.2.2)))
    (foldExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router left).1.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router right).1.2.1)
    (workExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router left).1.2.2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router right).1.2.2.2.1) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router right).1 := by
  let leftRaw :=
    exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router left
  let rightRaw :=
    exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router right
  change leftRaw.1 = rightRaw.1
  change (leftRaw.1.1, (leftRaw.1.2.2.1, leftRaw.1.2.2.2.2)) =
    (rightRaw.1.1, (rightRaw.1.2.2.1, rightRaw.1.2.2.2.2)) at contextExact
  change leftRaw.1.2.1 = rightRaw.1.2.1 at foldExact
  change leftRaw.1.2.2.2.1 = rightRaw.1.2.2.2.1 at workExact
  apply Prod.ext
  · exact congrArg (fun value => value.1) contextExact
  · apply Prod.ext
    · exact foldExact
    · apply Prod.ext
      · exact congrArg (fun value => value.2.1) contextExact
      · apply Prod.ext
        · exact workExact
        · exact congrArg (fun value => value.2.2) contextExact

#print axioms candidate_context_fold_work_eq_implies_base_coordinates_eq

end AspisK1.V7Tag73K13CandidateFibreBaseCoordinates
