import ExtractedVerifyFinishReachability
import SemanticRoundAlphaSelectedCanonical
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSemanticFinish
open Aeneas Aeneas.Std Result
theorem alpha_selected_canonical_of_finish_success
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hfinish : AspisR1PublicPreparation.FinishModel.finish
      R B D pub pre before challenges obs = ok (.Ok out)) :
    ∀ i : Fin 10,
      AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.SelectedCanonical
        (AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.ToSelected (out.alpha.val[i.val]'(by
          simpa [out.alpha.property] using i.isLt))) := by
  obtain ⟨running, afterRounds, record25, record26, z0, after25, z1, after26,
      hrounds, hchallenges, hstate, htranscript, hclaims, hrecord25, hextra,
      hcircle25, hrecord26, hbeforeZ1, hcircle26, hz⟩ :=
    AspisR1PublicPreparation.FinishCalls.finish_success R B D pub pre before
      challenges obs out hfinish
  exact AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
    R D pre before afterRounds running out.alpha hrounds

#print axioms alpha_selected_canonical_of_finish_success
end AspisR1.CuSavingsRetainedSemanticFinish
