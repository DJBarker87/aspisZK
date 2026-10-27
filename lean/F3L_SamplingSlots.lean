import F3K_OpeningCalls
set_option autoImplicit false
namespace AspisR1.F3L_SamplingSlots
open AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared

theorem ordinary : closedHashBoundaries.sampling.ordinary =
    AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic := rfl

theorem gamma : closedHashBoundaries.sampling.gamma =
    AspisR1ClaimPreparedBridge.candidateGammaPublic := rfl

#print axioms ordinary
#print axioms gamma
#print AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
#print AspisR1ClaimPreparedBridge.candidateGammaPublic
#print AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries
end AspisR1.F3L_SamplingSlots
