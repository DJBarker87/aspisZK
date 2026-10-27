import RPt_FIq_S_RawActualAnnotatedPolynomialRowAgreementConsumer
import R1SemanticPayloadView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIq_TypedPolynomials
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun RawActualAnnotatedTypedRows

/-- Each reached polynomial is the coefficient polynomial at its own actual
row in the SAME complete parsed source prefix. The constructor identity and
all canonical/decoder obligations are derived by the imported source proofs. -/
theorem same_entry {H : Type} (bytes : Slice U8) (pre : r1_wire.Prefix)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (D : aspis_core.Digest32 H) (initial final : RawActualAnnotatedPolynomialRun.Outcome H)
    (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (entry : RoundEvidence D pre) (mem : entry ∈ entries) :
    (polynomialOf entry.coefficients).map
      (algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact)=
      SemanticCoefficientCodec.polynomial
        (SemanticPayloadView.coeffAt values ⟨entry.round.val,entry_schedule_round_lt run entry mem⟩) := by
  exact RawActualAnnotatedPolynomialRowAgreementConsumer.annotated_entry_polynomial_agrees
    bytes pre values full D initial final entries run entry mem
    (SemanticPayloadView.coeffAt values ⟨entry.round.val,entry_schedule_round_lt run entry mem⟩)
    (SemanticPayloadView.coeffAt_payload values ⟨entry.round.val,entry_schedule_round_lt run entry mem⟩)

#print axioms same_entry
end AspisR1.FIq_TypedPolynomials
end
