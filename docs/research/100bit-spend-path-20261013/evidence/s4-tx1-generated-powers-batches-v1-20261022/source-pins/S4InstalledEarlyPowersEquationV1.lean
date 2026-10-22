import CurrentPreparedInstalledMeaning
import CurrentPreparedConcreteBoundaries
import CurrentClaimPowersInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4InstalledEarlyPowersEquationV1
open AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.ClaimPowers

/-- The powers callback in the exact installed Prepared.new boundary is the
    full-Result early-indexed generated candidate, through the retained public,
    claim, and LoopPowers carrier maps. `installedBoundaries` affects sampling
    leaves, not this `concreteBoundaries` field. -/
theorem installed_powers_eq_early_result
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :
    (AspisR1ClaimPreparedBridge.concreteBoundaries
      (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed)).powers
        29#usize x =
      (do
        let raw ← AspisR1LoopPowers.weights.early_powers 29#usize
          (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
            (AspisR1ClaimPreparedBridge.toClaimE x))
        .ok (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.fromClaimE
          (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw))) := by
  cases hearly : AspisR1LoopPowers.weights.early_powers 29#usize
      (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
        (AspisR1ClaimPreparedBridge.toClaimE x)) <;>
    simp [AspisR1ClaimPreparedBridge.concreteBoundaries,
      AspisR1ClaimPreparedBridge.powersPublic,
      AspisR1CurrentPreparedClaim.ClaimPowers.powers, hearly]

#print axioms installed_powers_eq_early_result
end AspisR1S4InstalledEarlyPowersEquationV1
