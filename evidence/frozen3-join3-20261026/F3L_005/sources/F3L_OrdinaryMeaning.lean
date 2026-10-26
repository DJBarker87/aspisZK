import CurrentPreparedOrdinaryRankV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OrdinaryMeaning
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge

theorem value (block : Array U8 32#usize)
    (out : AspisR1PublicPreparation.aspis_core.field.WideExact)
    (success : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=ok out) :
    decode (toClaimE out)=R0C.ModuloField.ordinary (decodeState block) := by
  obtain ⟨r,rank,decoded⟩ :=
    AspisR1Post25SamplerOrdinaryRankV1.candidateOrdinaryPublic_success_rank block out success
  rw [decoded]
  apply congrArg R0C.ModuloField.fieldRank
  apply Fin.ext
  exact rank

#print axioms value
end AspisR1.F3L_OrdinaryMeaning
end
