import CurrentPreparedJointRankMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1Post25SamplerOrdinaryRankV1
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
noncomputable section
attribute [local instance] Classical.propDecidable
local notation "Wide" => aspis_core.field.WideExact

theorem ordinary_rank_is_model (block : Array U8 32#usize) (out : Wide)
    (h : OrdinaryRankMeaning block out) :
    decode (toClaimE out)=R0C.ModuloField.ordinary (decodeState block) := by
  obtain ⟨r,hr,hd⟩ := h
  rw [hd]
  apply congrArg R0C.ModuloField.fieldRank
  apply Fin.ext
  exact hr

theorem gamma_rank_is_model (block : Array U8 32#usize) (out : Wide)
    (h : GammaRankMeaning block out) :
    decode (toClaimE out)=R0C.ModuloField.gamma (decodeState block) := by
  obtain ⟨r,hr,hd⟩ := h
  rw [hd]
  unfold R0C.ModuloField.gamma R0C.ModuloField.gammaNZ R0C.ModuloField.nonzeroRank
    R0C.ModuloField.positiveRanks
  change R0C.ModuloField.fieldRank r=R0C.ModuloField.fieldRank _
  apply congrArg R0C.ModuloField.fieldRank
  apply Fin.ext
  exact hr

theorem gamma_rank_nonzero (block : Array U8 32#usize) (out : Wide)
    (h : GammaRankMeaning block out) : decode (toClaimE out)≠0 := by
  rw [gamma_rank_is_model block out h]
  exact R0C.ModuloField.gamma_ne_zero _

theorem gamma_event_of_source_calls (value : State → Wide)
    (hcalls : ∀ s,candidateGammaPublic (encodeState s)=ok (value s))
    (bad : Finset AspisWideTower.WideExact) :
    AspisV8R19.OracleResampling.mean (fun s => FS.indicator (decode (toClaimE (value s))∈bad)) ≤
      bad.card * (257 / (256^32 : ℚ)) := by
  have he (s : State) : decode (toClaimE (value s))=R0C.ModuloField.gamma s := by
    have h := gamma_rank_is_model (encodeState s) (value s)
      (candidateGammaPublic_success_rank (encodeState s) (value s) (hcalls s))
    simpa only [state_roundtrip] using h
  simpa only [he] using R0C.ModuloField.gamma_event bad

theorem ordinary_event_of_source_calls (value : State → Wide)
    (hcalls : ∀ s,AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
      (encodeState s)=ok (value s))
    (bad : Finset AspisWideTower.WideExact) :
    AspisV8R19.OracleResampling.mean (fun s => FS.indicator (decode (toClaimE (value s))∈bad)) ≤
      bad.card * (257 / (256^32 : ℚ)) := by
  have he (s : State) : decode (toClaimE (value s))=R0C.ModuloField.ordinary s := by
    have h := ordinary_rank_is_model (encodeState s) (value s)
      (candidateOrdinaryPublic_success_rank (encodeState s) (value s) (hcalls s))
    simpa only [state_roundtrip] using h
  simpa only [he] using R0C.ModuloField.ordinary_event bad

#print axioms ordinary_rank_is_model
#print axioms gamma_rank_is_model
#print axioms gamma_rank_nonzero
#print axioms gamma_event_of_source_calls
#print axioms ordinary_event_of_source_calls
end
end AspisR1ClaimPreparedBridge.InstalledMeaning
