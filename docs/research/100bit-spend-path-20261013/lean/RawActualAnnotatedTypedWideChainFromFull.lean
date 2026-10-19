import RawActualAnnotatedTypedWideChain
import RawSemanticPrefixPolynomialRows

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedTypedWideChainFromFull

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualAnnotatedTypedRows
open AspisR1PublicPreparation.RawActualAnnotatedTypedWideChain

abbrev E := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

/-- The fixed typed full-prefix values themselves select the coefficient
vector at each reached round. The row codec forces the polynomial constructor,
so no arbitrary polynomial/value compatibility premise remains. -/
theorem annotatedRun_to_typed_wide_chain_from_full {H : Type}
    (bytes : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (values : AspisR1.SemanticPrefixCodec.Full)
    (hfull : AspisR1.SemanticPrefixCodec.encodeFull values =
      AspisR1PublicPreparation.PrefixAdapter.completedRecords pre)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (initial final : AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun.Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final entries) :
    AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain.Chain
      (algebraMap E W (DecodeMain initial.1))
      (algebraMap E W (DecodeMain final.1))
      (entries.map fun entry =>
        (AspisR1.SemanticCoefficientCodec.polynomial
          (AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt
            values ⟨entry.round.val % 10, Nat.mod_lt _ (by omega)⟩),
          algebraMap E W (challengeOf entry.q))) := by
  apply annotatedRun_to_typed_wide_chain bytes pre values hfull D initial final entries hrun
    (fun entry => AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt
      values ⟨entry.round.val % 10, Nat.mod_lt _ (by omega)⟩)
  intro entry hentry
  have hlt := entry_schedule_round_lt hrun entry hentry
  have hrow := AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt_payload
    values ⟨entry.round.val, hlt⟩
  have hmod : entry.round.val % 10 = entry.round.val := Nat.mod_eq_of_lt hlt
  have hfin : (⟨entry.round.val % 10, Nat.mod_lt _ (by omega)⟩ : Fin 10) =
      ⟨entry.round.val, hlt⟩ := Fin.ext hmod
  simpa [hfin] using hrow

#print axioms annotatedRun_to_typed_wide_chain_from_full
end AspisR1PublicPreparation.RawActualAnnotatedTypedWideChainFromFull
end
