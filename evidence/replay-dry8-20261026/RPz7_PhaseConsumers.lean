import RPz7_S1SemanticCodeVerifyV1
import RPz7_S1SemanticCodeFinishV1
set_option autoImplicit false
namespace RPz7_PhaseIso
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
theorem retained_carrier_RPz7 : Phase = FirstCaller.Phase := rfl

/-- The source mark ignores its observer; transport preserves that exact result. -/
theorem mark_transport_RPz7 (obs : Option (Phase → Result Unit)) (i : U8) :
    VerifyPrefix.mark (observerToFirst (observerToVerifier obs)) i =
      VerifyPrefix.mark obs i := by
  rw [observer_first_roundtrip_RPz7]

theorem verify_transport_RPz7 (F : VerifyPrefix.Finish) {H : Type}
    (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (Phase → Result Unit)) :
    VerifyPrefix.verify F D pub bytes hash (observerToFirst (observerToVerifier obs)) =
      VerifyPrefix.verify F D pub bytes hash obs := by
  rw [observer_first_roundtrip_RPz7]

theorem finish_transport_RPz7 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (tr : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (Phase → Result Unit)) :
    FinishModel.finish R B D pub pre tr ch (observerToFirst (observerToVerifier obs)) =
      FinishModel.finish R B D pub pre tr ch obs := by
  rw [observer_first_roundtrip_RPz7]

theorem code_finish_transport_RPz7 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (tr : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (Phase → Result Unit)) :
    S1SemanticCode.finish R B D pub pre tr ch (observerToFirst (observerToVerifier obs)) =
      S1SemanticCode.finish R B D pub pre tr ch obs := by
  rw [observer_first_roundtrip_RPz7]

theorem code_verify_transport_RPz7 (F : S1SemanticCode.Finish) {H : Type}
    (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (Phase → Result Unit)) :
    S1SemanticCode.verify F D pub bytes hash (observerToFirst (observerToVerifier obs)) =
      S1SemanticCode.verify F D pub bytes hash obs := by
  rw [observer_first_roundtrip_RPz7]

/-- The new transport laws have an actual constructor witness; this is not
a joint witness for the deployment security premises. -/
theorem phase_nonvacuity_RPz7 :
    ∃ p : verifier.Phase, toVerifier (toFirst p) = p :=
  ⟨.Parsed, rfl⟩

#print axioms retained_carrier_RPz7
#print axioms phase_nonvacuity_RPz7
#print axioms mark_transport_RPz7
#print axioms verify_transport_RPz7
#print axioms finish_transport_RPz7
#print axioms code_finish_transport_RPz7
#print axioms code_verify_transport_RPz7
end RPz7_PhaseIso
