import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9CandidateHelperV1.Funs
import S9PairCallerCandidateMapV1
import S9CandidateFoldMapPrimitivesV1
import S9CandidateBodyTermsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairTermPrefixMapV1

abbrev U := Std.Usize
abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CandidateW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev CandidateQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev Tuple4 (α : Type) := α × α × α × α
abbrev PairPrefixResult := U × Tuple4 PairW
abbrev CandidatePrefixResult := U × Tuple4 CandidateW

open AspisR1S9PairCallerCandidateMapV1
open AspisR1S9CandidateFoldMapPrimitivesV1

theorem mapResult_id {A : Type} (r : Result A) : AspisR1S9CandidateFoldMapPrimitivesV1.mapResult id r = r := by
  cases r <;> rfl

def mapPairTermCall (x : U × PairW) : U × CandidateW :=
  (x.1, pairToCandidateW x.2)

def mapPairTermTuple (x : Tuple4 PairW) : Tuple4 CandidateW :=
  (pairToCandidateW x.1, pairToCandidateW x.2.1,
   pairToCandidateW x.2.2.1, pairToCandidateW x.2.2.2)

def mapPairPrefixResult (x : PairPrefixResult) : CandidatePrefixResult :=
  (x.1, mapPairTermTuple x.2)

theorem pair_perm_quarter_maps_to_candidate :
    pairToCandidateM _root_.AspisR1S9PairCallerStepV1.weights.QUARTER =
      _root_.AspisR1S9CandidateHelperV1.weights.QUARTER := by
  unfold pairToCandidateM _root_.AspisR1S9PairCallerStepV1.toP6M
    _root_.AspisR1S9CandidateHelperV1.fromP6M
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
    _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
  rfl


private theorem pairToCandidateQ_one :
    pairToCandidateQ _root_.AspisR1S9PairCallerStepV1.field.QM31.ONE =
      _root_.AspisR1S9CandidateHelperV1.field.QM31.ONE := by
  unfold pairToCandidateQ _root_.AspisR1S9PairCallerStepV1.toP6Q
    _root_.AspisR1S9CandidateHelperV1.fromP6Q
    _root_.AspisR1S9PairCallerStepV1.field.QM31.ONE
    _root_.AspisR1S9CandidateHelperV1.field.QM31.ONE
    _root_.AspisR1S9PairCallerStepV1.toP6CM _root_.AspisR1S9CandidateHelperV1.fromP6CM
    _root_.AspisR1S9PairCallerStepV1.toP6M _root_.AspisR1S9CandidateHelperV1.fromP6M
  rfl

private theorem pair_map_make4 (q41 q8 q12 : PairQ) :
    mapArray pairToCandidateQ
      (Array.make 4#usize [_root_.AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12]) =
      _root_.AspisR1S9CandidateBodyTermsV1.candidateHigh
        (pairToCandidateQ q41) (pairToCandidateQ q8) (pairToCandidateQ q12) := by
  unfold mapArray Array.make _root_.AspisR1S9CandidateBodyTermsV1.candidateHigh
  simp only [pairToCandidateQ_one, List.map_cons, List.map_nil]
  rfl

def pairTermAt (ap1 : Array PairW (4#usize))
    (high : Array PairQ (4#usize)) (i : U) : Result (U × PairW) := do
  let perm ← Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM i
  let input ← Array.index_usize ap1 perm
  let coefficient ← Array.index_usize high i
  let product ← AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 input coefficient
  let term ← AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  ok (perm, term)

def candidateTermAt (ap1 : Array CandidateW (4#usize))
    (high : Array CandidateQ (4#usize)) (i : U) : Result (U × CandidateW) := do
  let perm ← Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM i
  let input ← Array.index_usize ap1 perm
  let coefficient ← Array.index_usize high i
  let product ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 input coefficient
  let term ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 product
    _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
  ok (perm, term)

theorem pair_term_at_maps_to_candidate
    (ap1 : Array PairW (4#usize)) (high : Array PairQ (4#usize)) (i : U) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapPairTermCall (pairTermAt ap1 high i) =
      candidateTermAt (mapArray pairToCandidateW ap1)
        (mapArray pairToCandidateQ high) i := by
  have hperms : _root_.AspisR1S9PairCallerStepV1.weights.PERM =
      _root_.AspisR1S9CandidateHelperV1.weights.PERM := by
    unfold _root_.AspisR1S9PairCallerStepV1.weights.PERM
      _root_.AspisR1S9CandidateHelperV1.weights.PERM
    rfl
  unfold pairTermAt candidateTermAt
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr (f := mapPairTermCall) (g := id)
  · rw [mapResult_id, hperms]
  · intro perm
    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr (f := mapPairTermCall) (g := pairToCandidateW)
    · exact mapArray_index_result pairToCandidateW ap1 perm
    · intro input
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr (f := mapPairTermCall) (g := pairToCandidateQ)
      · exact mapArray_index_result pairToCandidateQ high i
      · intro coefficient
        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr (f := mapPairTermCall) (g := pairToCandidateW)
        · exact pair_wide_mul_qm31_maps_to_candidate input coefficient
        · intro product
          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr (f := mapPairTermCall) (g := pairToCandidateW)
          · calc
              AspisR1S9CandidateFoldMapPrimitivesV1.mapResult pairToCandidateW
                  (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
                    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) =
                AspisR1S9PairCallerCandidateMapV1.mapResult pairToCandidateW
                  (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
                    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) := by
                      cases AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
                        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER <;> rfl
              _ = AspisR1S9CandidateHelperV1.field.WideExact.mul_m31
                    (pairToCandidateW product)
                    _root_.AspisR1S9CandidateHelperV1.weights.QUARTER := by
                      simpa only [pair_perm_quarter_maps_to_candidate] using
                        pair_wide_mul_m31_maps_to_candidate product
                          _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
          · intro term
            simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult, mapPairTermCall]


def pairTermPrefix (ap1 : Array PairW (4#usize))
    (q41 q8 q12 : PairQ) : Result PairPrefixResult := do
  let high := Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12]
  let r0 ← pairTermAt ap1 high 0#usize
  let r1 ← pairTermAt ap1 high 1#usize
  let r2 ← pairTermAt ap1 high 2#usize
  let r3 ← pairTermAt ap1 high 3#usize
  ok (r3.1,(r0.2,r1.2,r2.2,r3.2))

def candidateTermPrefix (ap1 : Array CandidateW (4#usize))
    (q41 q8 q12 : CandidateQ) : Result CandidatePrefixResult := do
  let high := AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12
  let r0 ← candidateTermAt ap1 high 0#usize
  let r1 ← candidateTermAt ap1 high 1#usize
  let r2 ← candidateTermAt ap1 high 2#usize
  let r3 ← candidateTermAt ap1 high 3#usize
  ok (r3.1,(r0.2,r1.2,r2.2,r3.2))

theorem pair_term_prefix_maps_to_candidate
    (ap1 : Array PairW (4#usize)) (q41 q8 q12 : PairQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapPairPrefixResult (pairTermPrefix ap1 q41 q8 q12) =
    candidateTermPrefix (mapArray pairToCandidateW ap1)
      (pairToCandidateQ q41) (pairToCandidateQ q8) (pairToCandidateQ q12) := by
  unfold pairTermPrefix candidateTermPrefix
  have hhigh := pair_map_make4 q41 q8 q12
  rw [← hhigh]
  dsimp only
  refine AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (f := mapPairPrefixResult) (g := mapPairTermCall) _ _ _ _ ?_ ?_
  · exact pair_term_at_maps_to_candidate ap1 _ 0#usize
  · intro r0
    refine AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (f := mapPairPrefixResult) (g := mapPairTermCall) _ _ _ _ ?_ ?_
    · exact pair_term_at_maps_to_candidate ap1 _ 1#usize
    · intro r1
      refine AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (f := mapPairPrefixResult) (g := mapPairTermCall) _ _ _ _ ?_ ?_
      · exact pair_term_at_maps_to_candidate ap1 _ 2#usize
      · intro r2
        refine AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
          (f := mapPairPrefixResult) (g := mapPairTermCall) _ _ _ _ ?_ ?_
        · exact pair_term_at_maps_to_candidate ap1 _ 3#usize
        · intro r3
          rfl

#print axioms pair_term_at_maps_to_candidate
#print axioms pair_perm_quarter_maps_to_candidate
#print axioms pair_term_prefix_maps_to_candidate

end AspisR1S9PairTermPrefixMapV1
