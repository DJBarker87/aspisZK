import RawActualInitialClaimFromFull
import RawActualAnnotatedTypedWideChainFromFull
import RawActualAnnotatedChallengeSequence

/-! One accepted strict prefix and one successful actual round execution
supply a typed WideExact sumcheck chain starting at that prefix's mask-sum
claim, with exactly the returned ordered alpha challenges. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedSemanticChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

abbrev K := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

def typedPairs {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (values : AspisR1.SemanticPrefixCodec.Full) (entries : List (RoundEvidence D pre)) :
    List (Polynomial W × W) :=
  entries.map fun entry =>
    (AspisR1.SemanticCoefficientCodec.polynomial
      (RawSemanticPrefixPolynomialRows.coefficientsAt values
        ⟨entry.round.val % 10, Nat.mod_lt _ (by omega)⟩),
      algebraMap K W (challengeOf entry.q))

/-- Shared parsing supplies the Full view; actual round success supplies the
initial decode, source annotations and alpha order. Neither endpoint nor the
per-round typed polynomial equations are assumed independently. -/
theorem parsed_rounds_typed_chain {H : Type}
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
        (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values).val
        (algebraMap K W (DecodeMain running))
        (typedPairs D pre values entries) := by
  obtain ⟨values,_hd,hfull,_he⟩ := PrefixAdapter.parse_typedFull bytes pre hparse
  obtain ⟨record,decoded,initial,entries,hrecord,hdecode,hindex,hrun,hqs⟩ :=
    RawActualAnnotatedChallengeSequence.rounds_success_annotated_challenges_eq_alpha
      D pre self afterRounds running alpha hrounds
  have hinit := RawActualInitialClaimFromFull.initial_claim_from_fixed_full
    pre values hfull record decoded initial hrecord hdecode hindex
  have hchain :=
    RawActualAnnotatedTypedWideChainFromFull.annotatedRun_to_typed_wide_chain_from_full
      bytes pre values hfull D
      (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, self)
      (running,alpha,afterRounds) entries hrun
  change RawGenericPolynomialSumcheckChain.Chain
    (algebraMap K W (DecodeMain initial))
    (algebraMap K W (DecodeMain running))
    (typedPairs D pre values entries) at hchain
  rw [hinit] at hchain
  exact ⟨values,initial,entries,hfull,hrun,hqs,hchain⟩

#print axioms parsed_rounds_typed_chain
end AspisR1PublicPreparation.RawActualParsedSemanticChain
end
