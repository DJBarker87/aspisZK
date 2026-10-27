import XRo_Join_PreparedScalars
import CurrentPreparedInstalledMeaning
import S1OriginalSerializerInstallationV1
import CurrentCompactInstalledPreparationV1
import S1ClosedPreparationInstallationV1
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRo_Join_Installed
open AspisR1CurrentCaller.InstalledPreparation AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning

/-- The dictionary used by F3M_JoinedClaim.on_run, not a free boundary. -/
def actual : AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
 concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling)
   AspisS1M31Embedding.Total.embed)

theorem powers_slot : actual.powers = powersPublic := rfl
theorem cached_claim_slot : @actual.claim = @claimPublic := rfl
theorem serializer_slot : actual.sampling.toBytes =
 AspisR1CurrentCaller.OriginalSerializerInstallation.sourceBytes := rfl

/-- Initialization has no sampler/claim callback; the SAME digest is used. -/
theorem start {H : Type} (D : C.D H) (hash : H) (state : Array U8 32#usize) (v : C.V) :
 mapR ct (XRn_Join_Release.transcript.Transcript.new (ed D) hash state (ev v)) =
 AspisR1PublicPreparation.transcript.Transcript.new D hash state v :=
 XRo_Join_Transcript.start D hash state v

/-- The actual scratch consumer never calls the historical gamma-taking slot. -/
theorem legacy_claim_unused
 (legacy : {H : Type} → C.D H → C.Sem H → Slice U8 → C.E → C.E → C.E →
   Result (core.result.Result C.E C.Err))
 {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (g : Array C.E 29#usize) :
 AspisR1PublicPreparation.PreparedScratchModel.prepare
   {actual with sampling:={actual.sampling with claim:=legacy}} D sem v hash g =
 AspisR1PublicPreparation.PreparedScratchModel.prepare actual D sem v hash g := rfl

#print axioms powers_slot
#print axioms cached_claim_slot
#print axioms serializer_slot
#print axioms start
#print axioms legacy_claim_unused
end XRo_Join_Installed
end
