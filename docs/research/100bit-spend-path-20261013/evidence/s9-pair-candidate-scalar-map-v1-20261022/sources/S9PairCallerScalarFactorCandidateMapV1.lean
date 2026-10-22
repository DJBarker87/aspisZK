import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9CandidateHelperV1.Funs
import AspisR1S9HelperP6.Funs
import S9PairCallerCandidateMapV1
import S9PairCallerScalarFactorFoldTransportV1
import S9CandidateScalarFactorFoldTransportV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerScalarFactorCandidateMapV1

abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev CandidateQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CandidateW := AspisR1S9CandidateHelperV1.field.WideExact

abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- The carrier maps compose pointwise on arrays, so both concrete generated
scalar folds land on the same selected P6 arrays. -/
theorem pair_q_array_maps_to_candidate_to_p6 (a : Array PairQ (4#usize)) :
    mapArray AspisR1S9CandidateHelperV1.toP6Q
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ a) =
      mapArray AspisR1S9PairCallerStepV1.toP6Q a := by
  cases a with
  | mk values hlen =>
      apply Subtype.ext
      change List.map AspisR1S9CandidateHelperV1.toP6Q
        (List.map AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ values) =
        List.map AspisR1S9PairCallerStepV1.toP6Q values
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateQ x

theorem pair_w_array_maps_to_candidate_to_p6 (a : Array PairW (4#usize)) :
    mapArray AspisR1S9CandidateHelperV1.toP6W
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW a) =
      mapArray AspisR1S9PairCallerStepV1.toP6W a := by
  cases a with
  | mk values hlen =>
      apply Subtype.ext
      change List.map AspisR1S9CandidateHelperV1.toP6W
        (List.map AspisR1S9PairCallerCandidateMapV1.pairToCandidateW values) =
        List.map AspisR1S9PairCallerStepV1.toP6W values
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW x

/-- Same generated `scalar_factor` result through Pair→P6 and Candidate→P6.
This is a full Result equality, including the failure and divergence cases. -/
theorem pair_scalar_factor_maps_to_candidate
    (f : Array PairQ (4#usize)) (p : Array PairW (4#usize)) :
    AspisR1S9PairCallerCandidateMapV1.mapResult
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
      (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor f p) =
    AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ f)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW p) := by
  apply AspisR1S9PairCallerCandidateMapV1.mapResult_injective
    AspisR1S9CandidateHelperV1.toP6W
    AspisR1S9PairCallerCandidateMapV1.candidateToP6_injective_W
  calc
    AspisR1S9PairCallerCandidateMapV1.mapResult AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9PairCallerCandidateMapV1.mapResult
          AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
          (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor f p)) =
      AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
        AspisR1S9PairCallerStepV1.toP6W
        (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor f p) := by
          cases h : AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor f p with
          | ok x =>
              change ok (AspisR1S9CandidateHelperV1.toP6W
                (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW x)) =
                ok (AspisR1S9PairCallerStepV1.toP6W x)
              exact congrArg Result.ok
                (AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW x)
          | fail e => rfl
          | div => rfl
    _ = @AspisR1S9HelperP6.weights.Weights.scalar_factor
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray AspisR1S9PairCallerStepV1.toP6Q f)
        (mapArray AspisR1S9PairCallerStepV1.toP6W p) :=
          AspisR1S9PairCallerScalarFactorFoldTransportV1.pair_scalar_factor_maps_to_p6 f p
    _ = AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
        AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ f)
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW p)) := by
          rw [← pair_q_array_maps_to_candidate_to_p6 f,
            ← pair_w_array_maps_to_candidate_to_p6 p]
          symm
          exact AspisR1S9CandidateScalarFactorFoldTransportV1.candidate_scalar_factor_maps_to_p6
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ f)
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW p)

end AspisR1S9PairCallerScalarFactorCandidateMapV1
