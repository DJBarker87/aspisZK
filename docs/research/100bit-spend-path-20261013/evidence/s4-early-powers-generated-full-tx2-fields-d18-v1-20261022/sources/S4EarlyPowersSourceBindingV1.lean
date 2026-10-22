import CurrentClaimPowersInstance
import S4P6PowersQueryJoinV1
import S4EarlyPowersPrefixTwelveFieldsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4EarlyPowersSourceBindingV1
open AspisR1S4P6PowersQueryJoinV1
/-- Direct typed carrier adapter around the extracted indexed `early_powers`
    body selected by the S1 early-return candidate. The tx2 caller invokes
    this at the source monomorphization N=29. -/
def extractedEarlyWeightsPowers (_N : Usize) (x : Stage2Wide) : Result Stage2Array := do
  let raw ← AspisR1LoopPowers.weights.early_powers 29#usize
    (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers (stage2ToClaim x))
  .ok (claimArrayToStage2 (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw))
/-- The emitted candidate body, mapped through the same source carriers, has
    exactly the result of the existing ClaimPowers instance, including errors
    and divergence; it is not just successful-output agreement. -/
theorem extractedEarlyWeightsPowers_eq_claimPowers (x : Stage2Wide) :
    extractedEarlyWeightsPowers 29#usize x = (do
      let values ← AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (stage2ToClaim x)
      .ok (claimArrayToStage2 values)) := by
  unfold extractedEarlyWeightsPowers AspisR1CurrentPreparedClaim.ClaimPowers.powers
  cases hearly : AspisR1LoopPowers.weights.early_powers 29#usize
      (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers (stage2ToClaim x)) <;>
    simp [hearly]
/-- The direct generated-body adapter is exactly the already-retained S4
    candidate slot; this is the slot binding used by the full tx2 cut. -/
theorem extractedEarlyWeightsPowers_eq_candidateSlot (x : Stage2Wide) :
    extractedEarlyWeightsPowers 29#usize x =
      AspisR1S4EarlyPowersPrefixTwelveFieldsRootV1.candidateEarlyWeightsPowers
        29#usize x := by
  unfold AspisR1S4EarlyPowersPrefixTwelveFieldsRootV1.candidateEarlyWeightsPowers
  exact extractedEarlyWeightsPowers_eq_claimPowers x
#print axioms extractedEarlyWeightsPowers_eq_claimPowers
#print axioms extractedEarlyWeightsPowers_eq_candidateSlot
end AspisR1S4EarlyPowersSourceBindingV1
