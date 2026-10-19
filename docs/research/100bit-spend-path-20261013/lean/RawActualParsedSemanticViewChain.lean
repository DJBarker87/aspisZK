import RawActualParsedSemanticChain
import RawSemanticPrefixMaskClaimView
import RawSemanticPrefixPolynomialViewCoefficients

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedSemanticViewChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain

def viewPairs {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (values : AspisR1.SemanticPrefixCodec.Full) (entries : List (RoundEvidence D pre)) :
    List (Polynomial W × W) :=
  entries.map fun entry =>
    (AspisR1.SemanticCoefficientCodec.polynomial
      (AspisR1.SemanticPayloadView.coeffAt values
        ⟨entry.round.val % 10, Nat.mod_lt _ (by omega)⟩),
      algebraMap K W (challengeOf entry.q))

theorem typedPairs_eq_viewPairs {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (values : AspisR1.SemanticPrefixCodec.Full)
    (entries : List (RoundEvidence D pre)) :
    typedPairs D pre values entries = viewPairs D pre values entries := by
  unfold typedPairs viewPairs
  apply List.map_congr_left
  intro entry hentry
  rw [RawSemanticPrefixPolynomialViewCoefficients.coefficientsAt_eq_coeffAt]

/-- Strict source parsing and actual rounds establish the sumcheck chain for
the retained semantic view's own claim and coefficient projections. The
literal transcript challenge/view coupling remains a separate source bridge. -/
theorem parsed_rounds_semantic_view_chain {H : Type}
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (D : aspis_core.Digest32 H)
    (self afterRounds : r1_wire.SemanticTranscript H)
    (running : MainQM) (alpha : Array MainQM 10#usize)
    (hrounds : RoundModel.rounds
      RawActualSemanticRoundCanonicality.actualRoundBoundaries D pre self =
      .ok (.Ok (running,alpha,afterRounds))) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full, ∃ initial : MainQM,
      ∃ entries : List (RoundEvidence D pre),
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, self)
        (running,alpha,afterRounds) entries ∧
      entries.map RoundEvidence.q = alpha.val ∧
      RawGenericPolynomialSumcheckChain.Chain
        (AspisR1.SemanticPayloadView.claimAt14 values)
        (algebraMap K W (DecodeMain running))
        (viewPairs D pre values entries) := by
  obtain ⟨values,initial,entries,hfull,hrun,hqs,hchain⟩ :=
    parsed_rounds_typed_chain bytes pre hparse D self afterRounds running alpha hrounds
  rw [AspisR1.RawSemanticPrefixMaskClaimView.claimAt14_val_eq_view,
    typedPairs_eq_viewPairs] at hchain
  exact ⟨values,initial,entries,hfull,hrun,hqs,hchain⟩

#print axioms typedPairs_eq_viewPairs
#print axioms parsed_rounds_semantic_view_chain
end AspisR1PublicPreparation.RawActualParsedSemanticViewChain
end
