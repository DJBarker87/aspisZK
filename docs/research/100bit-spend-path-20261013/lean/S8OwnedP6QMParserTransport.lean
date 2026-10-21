import S8OwnedP6FieldParserTransport

set_option autoImplicit false
namespace AspisR1.S8OwnedP6QMParserTransport
open Aeneas Aeneas.Std Result
open AspisR1.S8OwnedP6FieldParserTransport

theorem bind_mapResult {A B C : Type} (f : A → B) (r : Result A) (k : B → Result C) :
    (mapResult f r >>= k) = r >>= fun a => k (f a) := by
  cases r <;> rfl

theorem residual_q_eq (o : Option core.convert.Infallible) :
    mapResult (Option.map qToCandidate)
      (S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual ActualQ o) =
      AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual CandidateQ o := by
  cases o with
  | none =>
    simp [S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      massert, read_discriminant, S8OwnedP6.optionDiscriminant,
      AspisR1CandidateParser.optionDiscriminant, AspisR1CandidateParser.optionTag, mapResult]
  | some impossible => cases impossible

/-- Full result correspondence, including parser rejection, runtime failure
and divergence, to the already proved retained strict parser owner. -/
theorem qm_parser_eq (bytes : Slice U8) :
    mapResult (Option.map qToCandidate)
      (S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes) =
      AspisR1CandidateParser.field.QM31.from_le_bytes bytes := by
  unfold S8OwnedP6.aspis_core.field.QM31.from_le_bytes
    AspisR1CandidateParser.field.QM31.from_le_bytes
  simp only [mapResult_bind]
  apply bind_congr_right
  intro slice0
  rw [← cm_parser_eq]
  simp only [bind_mapResult, mapResult_bind]
  apply bind_congr_right
  intro opt0
  cases opt0 with
  | none =>
    simp only [Option.map, S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
    exact residual_q_eq none
  | some c0 =>
    simp only [Option.map, S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok,
      mapResult_bind]
    apply bind_congr_right
    intro slice1
    rw [← cm_parser_eq]
    simp only [bind_mapResult, mapResult_bind]
    apply bind_congr_right
    intro opt1
    cases opt1 with
    | none =>
      simp only [Option.map, S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
      exact residual_q_eq none
    | some c1 =>
      simp only [Option.map, S8OwnedP6.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
      rfl

theorem actual_qm_success_to_retained (bytes : Slice U8) (q : ActualQ)
    (h : S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes = .ok (some q)) :
    AspisR1CandidateParser.field.QM31.from_le_bytes bytes = .ok (some (qToCandidate q)) := by
  rw [← qm_parser_eq, h]
  rfl

#print axioms qm_parser_eq
#print axioms actual_qm_success_to_retained
#print axioms bind_mapResult
#print axioms residual_q_eq

end AspisR1.S8OwnedP6QMParserTransport
