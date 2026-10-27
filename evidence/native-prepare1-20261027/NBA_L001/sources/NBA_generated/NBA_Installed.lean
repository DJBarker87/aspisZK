import CurrentPreparedInstalledMeaning
import S1OriginalSerializerInstallationV1
import CurrentCompactInstalledPreparationV1
import S1ClosedPreparationInstallationV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_Installed
open AspisR1CurrentCaller.InstalledPreparation AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller.OriginalSerializerInstallation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning

/-- The adopted cohort dictionary, without an extraction join or kit. -/
def actual : AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
 concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling)
   AspisS1M31Embedding.Total.embed)

theorem powers_slot : actual.powers = powersPublic := rfl
theorem claim_slot : @actual.claim = @claimPublic := rfl
theorem serializer_slot : actual.sampling.toBytes =
 AspisR1CurrentCaller.OriginalSerializerInstallation.sourceBytes := rfl

#print axioms powers_slot
#print axioms claim_slot
#print axioms serializer_slot
end AspisR1.NBA_Installed
end
