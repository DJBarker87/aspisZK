import RawActualViewSourceChallenges

/-! Recover the actual ten polynomial challenges as the last ten source
challenges of the complete begin-plus-rounds log. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawFullTraceRoundChallenges
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

 theorem begin_challenge_length (challenges : r1_wire.Challenges) :
    (BeginCalls.challengeList challenges).length = 15 := by
  have hz : challenges.zc.val.length = 10 := challenges.zc.property
  simp only [BeginCalls.challengeList, List.length_cons, List.length_append, hz,
    List.length_nil]

 theorem full_trace_round_challenges {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (challenges : r1_wire.Challenges)
    (values : AspisR1.SemanticPrefixCodec.Full)
    (entries : List (RoundEvidence D pre)) (cs : List (SourceFull25.Call D pre))
    (hqs : cs.map SourceFull25.Call.q =
      BeginCalls.challengeList challenges ++ entries.map RoundEvidence.q) :
    (cs.drop 15).map SourceLiteralTraceLift.sourceChallenge =
      (viewPairs D pre values entries).map Prod.snd := by
  apply RawActualViewSourceChallenges.source_challenges_eq_viewPairs
  rw [List.map_drop, hqs, ← begin_challenge_length challenges]
  exact List.drop_left

#print axioms begin_challenge_length
#print axioms full_trace_round_challenges
end AspisR1PublicPreparation.RawFullTraceRoundChallenges
end
