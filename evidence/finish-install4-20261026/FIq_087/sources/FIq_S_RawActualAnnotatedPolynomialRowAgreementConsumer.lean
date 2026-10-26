import FIq_S_RawActualAnnotatedTypedRowReadback
import FIq_S_RawActualPolynomialRowAgreement

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedPolynomialRowAgreementConsumer

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedTypedRows
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

/-- A reached record's actual coefficients agree with the polynomial payload
of the same fixed typed Prefix value. The constructor premise is supplied by
`SemanticPayloadView.coeffAt_payload` in the thin view-specific caller. -/
theorem annotated_entry_polynomial_agrees {H : Type}
    (bytes : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (values : AspisR1.SemanticPrefixCodec.Full)
    (hfull : AspisR1.SemanticPrefixCodec.encodeFull values =
      AspisR1PublicPreparation.PrefixAdapter.completedRecords pre)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (initial final : AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun.Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final entries)
    (entry : RoundEvidence D pre) (hentry : entry ∈ entries)
    (coefficients : AspisR1.SemanticCoefficientCodec.Coefficients)
    (hpoly : (values ⟨15 + entry.round.val, by
        have hlt := entry_schedule_round_lt hrun entry hentry
        omega⟩).val =
      AspisR1.SemanticRecordCodec.Payload.polynomial coefficients) :
    (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
        entry.coefficients).map
      (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) =
      AspisR1.SemanticCoefficientCodec.polynomial coefficients := by
  have htyped := annotated_entry_decodes_parsed_row bytes pre values hfull
    D initial final entries hrun entry hentry
  exact AspisR1PublicPreparation.RawActualPolynomialRowAgreement.actual_polynomial_row_agrees
    ⟨15 + entry.round.val, by
      have hlt := entry_schedule_round_lt hrun entry hentry
      omega⟩ entry.record entry.coefficients (values ⟨15 + entry.round.val, by
        have hlt := entry_schedule_round_lt hrun entry hentry
        omega⟩) coefficients hpoly entry.decodeOk htyped

#print axioms annotated_entry_polynomial_agrees
end AspisR1PublicPreparation.RawActualAnnotatedPolynomialRowAgreementConsumer
