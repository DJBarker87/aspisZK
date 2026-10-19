import RawActualAnnotatedPolynomialWideChain
import RawActualAnnotatedPolynomialRowAgreementConsumer

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedTypedWideChain

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialWideChain
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRowAgreementConsumer
open AspisR1PublicPreparation.RawActualAnnotatedTypedRows

abbrev E := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

/-- Once each reached row is identified with its fixed parsed full-prefix
value, the actual decoded chain can replace its mapped coefficient polynomial
by that same typed row's WideExact polynomial. -/
theorem annotatedRun_to_typed_wide_chain {H : Type}
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
    (coefficients : RoundEvidence D pre → AspisR1.SemanticCoefficientCodec.Coefficients)
    (hpoly : ∀ (entry : RoundEvidence D pre) (hentry : entry ∈ entries),
      (values ⟨15 + entry.round.val, by
        have hlt := entry_schedule_round_lt hrun entry hentry
        omega⟩).val =
      AspisR1.SemanticRecordCodec.Payload.polynomial (coefficients entry)) :
    AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain.Chain
      (algebraMap E W (DecodeMain initial.1))
      (algebraMap E W (DecodeMain final.1))
      (entries.map fun entry =>
        (AspisR1.SemanticCoefficientCodec.polynomial (coefficients entry),
          algebraMap E W (challengeOf entry.q))) := by
  have hwide := annotatedRun_to_wide_chain D pre _ initial final entries hrun
  have hentries :
      entries.map (fun entry =>
        ((polynomialOf entry.coefficients).map (algebraMap E W),
          algebraMap E W (challengeOf entry.q))) =
      entries.map (fun entry =>
        (AspisR1.SemanticCoefficientCodec.polynomial (coefficients entry),
          algebraMap E W (challengeOf entry.q))) := by
    apply List.map_congr_left
    intro entry hentry
    have hpolyEntry := annotated_entry_polynomial_agrees bytes pre values hfull
      D initial final entries hrun entry hentry (coefficients entry)
      (hpoly entry hentry)
    exact congrArg (fun p : Polynomial W =>
      (p, algebraMap E W (challengeOf entry.q))) hpolyEntry
  simpa only [hentries] using hwide

#print axioms annotatedRun_to_typed_wide_chain

end AspisR1PublicPreparation.RawActualAnnotatedTypedWideChain
end
