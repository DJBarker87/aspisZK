import S9PairCallerBodyPrefixV1
import S9CandidateBodyPrefixV1
import S9PairCallerCandidateMapV1
import S9PairCallerScalarFactorCandidateMapV1
import S9CandidateFoldMapPrimitivesV1
import AspisR1S9HelperP6.Funs
import S9FactoredLoopBodyShapeV3

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9PairCallerActiveBodyMapV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev PairArray := Array AspisR1S9PairCallerStepV1.field.WideExact (4#usize)
abbrev CandidateArray := Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize)

abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9PairCallerCandidateMapV1.mapResult f

def pairToCandidateFlow :
    ControlFlow (R × PairArray) PairArray → ControlFlow (R × CandidateArray) CandidateArray
  | .cont (r, a) => .cont (r, mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW a)
  | .done a => .done (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW a)

private theorem pairToCandidateQ_one :
    AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        AspisR1S9PairCallerStepV1.field.QM31.ONE =
      AspisR1S9CandidateHelperV1.field.QM31.ONE := by
  unfold AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
    AspisR1S9PairCallerStepV1.toP6Q AspisR1S9CandidateHelperV1.fromP6Q
    AspisR1S9PairCallerStepV1.field.QM31.ONE
    AspisR1S9CandidateHelperV1.field.QM31.ONE
    AspisR1S9PairCallerStepV1.toP6CM AspisR1S9CandidateHelperV1.fromP6CM
    AspisR1S9PairCallerStepV1.toP6M AspisR1S9CandidateHelperV1.fromP6M
  rfl

private theorem pair_qm_mul_one_maps (x : AspisR1S9PairCallerStepV1.field.QM31) :
    AspisR1S9PairCallerCandidateMapV1.mapResult
        AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        (AspisR1S9PairCallerStepV1.field.QM31.mul
          AspisR1S9PairCallerStepV1.field.QM31.ONE x) =
      AspisR1S9CandidateHelperV1.field.QM31.mul
        AspisR1S9CandidateHelperV1.field.QM31.ONE
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x) := by
  calc
    AspisR1S9PairCallerCandidateMapV1.mapResult
        AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        (AspisR1S9PairCallerStepV1.field.QM31.mul
          AspisR1S9PairCallerStepV1.field.QM31.ONE x) =
      AspisR1S9CandidateHelperV1.field.QM31.mul
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
          AspisR1S9PairCallerStepV1.field.QM31.ONE)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x) :=
          AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate _ _
    _ = AspisR1S9CandidateHelperV1.field.QM31.mul
        AspisR1S9CandidateHelperV1.field.QM31.ONE
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x) := by
          rw [pairToCandidateQ_one]

private theorem pair_map_make4
    (q1 q2 q3 : AspisR1S9PairCallerStepV1.field.QM31) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        (Array.make 4#usize
          [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) =
      Array.make 4#usize
        [AspisR1S9CandidateHelperV1.field.QM31.ONE,
          AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q1,
          AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q2,
          AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q3] := by
  unfold AspisR1S9CandidateFoldMapPrimitivesV1.mapArray Array.make
  simp only [pairToCandidateQ_one, List.map_cons, List.map_nil]

/-- Prefix correspondence through the actual scalar-factor result. The sole
remaining premise is the Result-preserving correspondence for the retained
after-low continuation; all earlier binds are discharged from their concrete
operation and index maps. -/
theorem pair_active_body_maps_to_candidate_of_after_low
    (ap0 ap1 : PairArray) (extra : Array AspisR1S9PairCallerStepV1.field.QM31 (2#usize))
    (side : U) (iterNext : R) (weights : PairArray)
    (hafter : ∀ (q41 q8 q12 q16 : AspisR1S9PairCallerStepV1.field.QM31)
      (low : AspisR1S9PairCallerStepV1.field.WideExact),
      mapResult pairToCandidateFlow
        (AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
          ap1 side iterNext weights q41 q8 q12 q16 low) =
      AspisR1S9CandidateBodyPrefixV1.candidateAfterLow
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        side iterNext
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW weights)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q41)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q8)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q12)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q16)
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW low)) :
    mapResult pairToCandidateFlow
      (AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra side iterNext weights) =
      AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        side iterNext
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW weights) := by
  unfold AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
    AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
  · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra side
  · intro q
    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
    · exact pair_qm_mul_one_maps q
    · intro q1
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
      · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate q1 q
      · intro q2
        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
          pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate q2 q
        · intro q3
          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
            pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
          · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate q3 q
          · intro unusedQ4
            apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
              pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
            · simpa only [pair_map_make4] using
                AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
                  AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
                  (Array.make 4#usize
                    [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) 2#usize
            · intro q4
              apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
              · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_square_maps_to_candidate q4
              · intro q41
                apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                  pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
                · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_square_maps_to_candidate q41
                · intro q8
                  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                    pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
                  · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate q8 q41
                  · intro q12
                    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                      pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
                    · exact AspisR1S9PairCallerCandidateMapV1.pair_qm_square_maps_to_candidate q8
                    · intro q16
                      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                        pairToCandidateFlow AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
                      · change AspisR1S9PairCallerCandidateMapV1.mapResult
                          AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
                          (_root_.AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
                            (Array.make 4#usize
                              [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0) =
                          _root_.AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
                            (Array.make 4#usize
                              [AspisR1S9CandidateHelperV1.field.QM31.ONE,
                               AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q1,
                               AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q2,
                               AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q3])
                            (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
                        rw [← pair_map_make4]
                        exact AspisR1S9PairCallerScalarFactorCandidateMapV1.pair_scalar_factor_maps_to_candidate
                          (Array.make 4#usize
                            [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0
                      · intro low
                        exact hafter q41 q8 q12 q16 low

#print axioms pair_active_body_maps_to_candidate_of_after_low

end AspisR1S9PairCallerActiveBodyMapV1
