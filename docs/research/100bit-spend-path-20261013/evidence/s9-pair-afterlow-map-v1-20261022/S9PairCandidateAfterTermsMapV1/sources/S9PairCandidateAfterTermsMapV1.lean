import S9PairCallerBodyPrefixV1
import S9CandidateBodyTermsV1
import S9CandidateBodyPrefixV1
import S9PairTermPrefixMapV1
import S9PairCallerCandidateMapV1
import S9CandidateFoldMapPrimitivesV1
import S9CandidateUpdateResultMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9PairCandidateAfterTermsMapV1

open AspisR1S9PairCallerBodyPrefixV1
open AspisR1S9PairCallerStepV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9PairCallerCandidateMapV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev PU := AspisR1S9PairCallerBodyPrefixV1.U
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev PW := AspisR1S9PairCallerBodyPrefixV1.W
abbrev PQ := AspisR1S9PairCallerBodyPrefixV1.Q
abbrev CW := Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize)

def pairMapFlow (x : ControlFlow (PR × PW) PW) :
    ControlFlow (PR × CW) CW :=
  match x with
  | .cont (r, a) => .cont (r, mapArray pairToCandidateW a)
  | .done a => .done (mapArray pairToCandidateW a)

theorem pair_quarter_maps_to_candidate :
    pairToCandidateM _root_.AspisR1S9PairCallerStepV1.weights.QUARTER =
      _root_.AspisR1S9CandidateHelperV1.weights.QUARTER :=
  AspisR1S9PairTermPrefixMapV1.pair_perm_quarter_maps_to_candidate

/-- The exact Pair suffix after the four source terms have been computed.
The `perm3` argument is the value already read earlier in the same Pair body;
the Candidate implementation performs that read again in its branch. -/
def pairAfterTerms
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact)
    (perm3 : PU) (t0 t1 t2 t3 : AspisR1S9PairCallerStepV1.field.WideExact) :
    Result (ControlFlow (PR × PW) PW) := do
  let we8 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 0#usize
  let we9 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 1#usize
  let first2 ← AspisR1S9PairCallerStepV1.field.WideExact.add we8 we9
  let we10 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 2#usize
  let first3 ← AspisR1S9PairCallerStepV1.field.WideExact.add first2 we10
  let we11 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 3#usize
  let all ← AspisR1S9PairCallerStepV1.field.WideExact.add first3 we11
  if side = 0#usize then do
    let we12 ← AspisR1S9PairCallerStepV1.field.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we12
    let we13 ← AspisR1S9PairCallerStepV1.field.WideExact.mul low first3
    let we14 ← AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 we13 q16
    let a ← Array.update weights1 1#usize we14
    ok (cont (iterNext, a))
  else do
    let we12 ← Array.index_usize weights 1#usize
    let we13 ← Array.index_usize ap1 perm3
    let we14 ← AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we13
      _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
    let we15 ← AspisR1S9PairCallerStepV1.field.WideExact.mul low we14
    let we16 ← AspisR1S9PairCallerStepV1.field.WideExact.add we12 we15
    let weights1 ← Array.update weights 1#usize we16
    let we17 ← AspisR1S9PairCallerStepV1.field.WideExact.mul low all
    let we18 ← AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 we17 q41
    let weights2 ← Array.update weights1 2#usize we18
    let we19 ← AspisR1S9PairCallerStepV1.field.WideExact.mul low first2
    let q10 ← AspisR1S9PairCallerStepV1.field.QM31.mul q16 q41
    let we20 ← AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 we19 q10
    let a ← Array.update weights2 3#usize we20
    ok (cont (iterNext, a))

/-- Candidate's source-shaped continuation after term generation. It receives
and reuses the `perm3` value already bound by the fourth term call. -/
def candidateAfterTermsBound
    (ap1 : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (side : PU) (iterNext : PR)
    (weights : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (q41 q8 q12 q16 : AspisR1S9CandidateHelperV1.field.QM31)
    (low : AspisR1S9CandidateHelperV1.field.WideExact) (perm3 : PU)
    (t0 t1 t2 t3 : AspisR1S9CandidateHelperV1.field.WideExact) :
    Result (ControlFlow (PR × Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
      (Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))) := do
  let we8 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 0#usize
  let we9 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 1#usize
  let first2 ← AspisR1S9CandidateHelperV1.field.WideExact.add we8 we9
  let we10 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 2#usize
  let first3 ← AspisR1S9CandidateHelperV1.field.WideExact.add first2 we10
  let we11 ← Array.index_usize (Array.make 4#usize [t0,t1,t2,t3]) 3#usize
  let all ← AspisR1S9CandidateHelperV1.field.WideExact.add first3 we11
  if side = 0#usize then do
    let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we12
    let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
    let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
    let a ← Array.update weights1 1#usize we14
    ok (cont (iterNext,a))
  else do
    let we12 ← Array.index_usize weights 1#usize
    let we13 ← Array.index_usize ap1 perm3
    let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we13
      _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
    let we15 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we14
    let we16 ← AspisR1S9CandidateHelperV1.field.WideExact.add we12 we15
    let weights1 ← Array.update weights 1#usize we16
    let we17 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
    let we18 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we17 q41
    let weights2 ← Array.update weights1 2#usize we18
    let we19 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
    let q10 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
    let we20 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we19 q10
    let a ← Array.update weights2 3#usize we20
    ok (cont (iterNext,a))

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Split the original source continuation after its four interleaved term
calls. Both the term-prefix result and the tail equation come from inversion
of this one `pairAfterLow` run. This is the connector used by the caller
assembly; it does not posit a second successful execution. -/
theorem pair_after_low_terms_from_same_success
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact)
    (flow : ControlFlow (PR × PW) PW)
    (h : AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
      ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow) :
    ∃ (t0 t1 t2 t3 : AspisR1S9PairCallerStepV1.field.WideExact)
      (perm3 : PU),
      AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
        .ok (perm3,(t0,t1,t2,t3)) ∧
      Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM
        3#usize = .ok perm3 ∧
      pairAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low perm3
        t0 t1 t2 t3 = .ok flow := by
  have hcur := h
  unfold AspisR1S9PairCallerBodyPrefixV1.pairAfterLow at hcur
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 0#usize)
    _ _ hcur with ⟨i0,hi0,hcur⟩
  rcases bind_success_inv (Array.index_usize ap1 i0) _ _ hcur with
    ⟨x0,hx0,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize
      [field.QM31.ONE,q41,q8,q12]) 0#usize) _ _ hcur with
    ⟨a0,ha0,hcur⟩
  rcases bind_success_inv (field.WideExact.mul_qm31 x0 a0) _ _ hcur with
    ⟨m0,hm0,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m0 _root_.AspisR1S9PairCallerStepV1.weights.QUARTER)
    _ _ hcur with ⟨t0,ht0,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 1#usize)
    _ _ hcur with ⟨i1,hi1,hcur⟩
  rcases bind_success_inv (Array.index_usize ap1 i1) _ _ hcur with
    ⟨x1,hx1,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize
      [field.QM31.ONE,q41,q8,q12]) 1#usize) _ _ hcur with
    ⟨a1,ha1,hcur⟩
  rcases bind_success_inv (field.WideExact.mul_qm31 x1 a1) _ _ hcur with
    ⟨m1,hm1,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m1 _root_.AspisR1S9PairCallerStepV1.weights.QUARTER)
    _ _ hcur with ⟨t1,ht1,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 2#usize)
    _ _ hcur with ⟨i2,hi2,hcur⟩
  rcases bind_success_inv (Array.index_usize ap1 i2) _ _ hcur with
    ⟨x2,hx2,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize
      [field.QM31.ONE,q41,q8,q12]) 2#usize) _ _ hcur with
    ⟨a2,ha2,hcur⟩
  rcases bind_success_inv (field.WideExact.mul_qm31 x2 a2) _ _ hcur with
    ⟨m2,hm2,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m2 _root_.AspisR1S9PairCallerStepV1.weights.QUARTER)
    _ _ hcur with ⟨t2,ht2,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 3#usize)
    _ _ hcur with ⟨i3,hi3,hcur⟩
  rcases bind_success_inv (Array.index_usize ap1 i3) _ _ hcur with
    ⟨x3,hx3,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (Array.make 4#usize
      [field.QM31.ONE,q41,q8,q12]) 3#usize) _ _ hcur with
    ⟨a3,ha3,hcur⟩
  rcases bind_success_inv (field.WideExact.mul_qm31 x3 a3) _ _ hcur with
    ⟨m3,hm3,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m3 _root_.AspisR1S9PairCallerStepV1.weights.QUARTER)
    _ _ hcur with ⟨t3,ht3,hcur⟩
  change pairAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low i3
    t0 t1 t2 t3 = .ok flow at hcur
  have hterms : AspisR1S9PairTermPrefixMapV1.pairTermPrefix
      ap1 q41 q8 q12 = .ok (i3,(t0,t1,t2,t3)) := by
    unfold AspisR1S9PairTermPrefixMapV1.pairTermPrefix
      AspisR1S9PairTermPrefixMapV1.pairTermAt
    simp [hi0,hx0,ha0,hm0,ht0,hi1,hx1,ha1,hm1,ht1,
      hi2,hx2,ha2,hm2,ht2,hi3,hx3,ha3,hm3,ht3]
  exact ⟨t0,t1,t2,t3,i3,hterms,hi3,hcur⟩

#print axioms pair_after_low_terms_from_same_success


/-- Universal Pair-to-Candidate map for the exact suffix, with the same
already-bound `perm3` on both sides. -/
theorem pair_after_terms_bound_result_maps
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact)
    (perm3 : PU) (t0 t1 t2 t3 : AspisR1S9PairCallerStepV1.field.WideExact) :
    AspisR1S9PairCallerCandidateMapV1.mapResult pairMapFlow
      (pairAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3) =
    candidateAfterTermsBound
      (mapArray pairToCandidateW ap1) side iterNext (mapArray pairToCandidateW weights)
      (pairToCandidateQ q41) (pairToCandidateQ q8) (pairToCandidateQ q12)
      (pairToCandidateQ q16) (pairToCandidateW low) perm3
      (pairToCandidateW t0) (pairToCandidateW t1) (pairToCandidateW t2)
      (pairToCandidateW t3) := by
  unfold pairAfterTerms candidateAfterTermsBound
  by_cases hside : side = 0#usize
  · simp only [if_pos hside, if_true]
    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (f := pairMapFlow) (g := pairToCandidateW)
    · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 0#usize
    · intro we8
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (f := pairMapFlow) (g := pairToCandidateW)
      · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 1#usize
      · intro we9
        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
          (f := pairMapFlow) (g := pairToCandidateW)
        · exact pair_wide_add_maps_to_candidate we8 we9
        · intro first2
          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
            (f := pairMapFlow) (g := pairToCandidateW)
          · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 2#usize
          · intro we10
            apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
              (f := pairMapFlow) (g := pairToCandidateW)
            · exact pair_wide_add_maps_to_candidate first2 we10
            · intro first3
              apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                (f := pairMapFlow) (g := pairToCandidateW)
              · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 3#usize
              · intro we11
                apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                  (f := pairMapFlow) (g := pairToCandidateW)
                · exact pair_wide_add_maps_to_candidate first3 we11
                · intro all
                  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                    (f := pairMapFlow) (g := pairToCandidateW)
                  · exact pair_wide_mul_maps_to_candidate low all
                  · intro we12
                    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                      (f := pairMapFlow) (g := (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray pairToCandidateW))
                    · exact AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result pairToCandidateW (weights) 0#usize we12 (by decide)
                    · intro weights1
                      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                        (f := pairMapFlow) (g := pairToCandidateW)
                      · exact pair_wide_mul_maps_to_candidate low first3
                      · intro we13
                        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                          (f := pairMapFlow) (g := pairToCandidateW)
                        · exact pair_wide_mul_qm31_maps_to_candidate we13 q16
                        · intro we14
                          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                            (f := pairMapFlow) (g := (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray pairToCandidateW))
                          · exact AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result pairToCandidateW (weights1) 1#usize we14 (by decide)
                          · intro a
                            rfl
  · have hne : side ≠ 0#usize := hside
    simp only [if_neg hne, if_false]
    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (f := pairMapFlow) (g := pairToCandidateW)
    · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 0#usize
    · intro we8
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (f := pairMapFlow) (g := pairToCandidateW)
      · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 1#usize
      · intro we9
        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
          (f := pairMapFlow) (g := pairToCandidateW)
        · exact pair_wide_add_maps_to_candidate we8 we9
        · intro first2
          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
            (f := pairMapFlow) (g := pairToCandidateW)
          · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 2#usize
          · intro we10
            apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
              (f := pairMapFlow) (g := pairToCandidateW)
            · exact pair_wide_add_maps_to_candidate first2 we10
            · intro first3
              apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                (f := pairMapFlow) (g := pairToCandidateW)
              · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW (Array.make 4#usize [t0,t1,t2,t3]) 3#usize
              · intro we11
                apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                  (f := pairMapFlow) (g := pairToCandidateW)
                · exact pair_wide_add_maps_to_candidate first3 we11
                · intro all
                  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                    (f := pairMapFlow) (g := pairToCandidateW)
                  · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW weights 1#usize
                  · intro we12
                    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                      (f := pairMapFlow) (g := pairToCandidateW)
                    · exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result pairToCandidateW ap1 perm3
                    · intro we13
                      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                        (f := pairMapFlow) (g := pairToCandidateW)
                      · calc
                          AspisR1S9CandidateFoldMapPrimitivesV1.mapResult pairToCandidateW
                              (_root_.AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we13
                                _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) =
                              AspisR1S9PairCallerCandidateMapV1.mapResult pairToCandidateW
                                (_root_.AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we13
                                  _root_.AspisR1S9PairCallerStepV1.weights.QUARTER) := by
                                    cases _root_.AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 we13
                                      _root_.AspisR1S9PairCallerStepV1.weights.QUARTER <;> rfl
                          _ = _root_.AspisR1S9CandidateHelperV1.field.WideExact.mul_m31
                              (pairToCandidateW we13)
                              (_root_.AspisR1S9CandidateHelperV1.weights.QUARTER) := by
                                simpa only [AspisR1S9PairTermPrefixMapV1.pair_perm_quarter_maps_to_candidate]
                                  using pair_wide_mul_m31_maps_to_candidate we13
                                    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
                      · intro we14
                        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                          (f := pairMapFlow) (g := pairToCandidateW)
                        · exact pair_wide_mul_maps_to_candidate low we14
                        · intro we15
                          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                            (f := pairMapFlow) (g := pairToCandidateW)
                          · exact pair_wide_add_maps_to_candidate we12 we15
                          · intro we16
                            apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                              (f := pairMapFlow) (g := (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray pairToCandidateW))
                            · exact AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result pairToCandidateW (weights) 1#usize we16 (by decide)
                            · intro weights1
                              apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                (f := pairMapFlow) (g := pairToCandidateW)
                              · exact pair_wide_mul_maps_to_candidate low all
                              · intro we17
                                apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                  (f := pairMapFlow) (g := pairToCandidateW)
                                · exact pair_wide_mul_qm31_maps_to_candidate we17 q41
                                · intro we18
                                  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                    (f := pairMapFlow) (g := (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray pairToCandidateW))
                                  · exact AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result pairToCandidateW (weights1) 2#usize we18 (by decide)
                                  · intro weights2
                                    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                      (f := pairMapFlow) (g := pairToCandidateW)
                                    · exact pair_wide_mul_maps_to_candidate low first2
                                    · intro we19
                                      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                        (f := pairMapFlow) (g := pairToCandidateQ)
                                      · exact pair_qm_mul_maps_to_candidate q16 q41
                                      · intro q10
                                        apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                          (f := pairMapFlow) (g := pairToCandidateW)
                                        · exact pair_wide_mul_qm31_maps_to_candidate we19 q10
                                        · intro we20
                                          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
                                            (f := pairMapFlow) (g := (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray pairToCandidateW))
                                          · exact AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result pairToCandidateW (weights2) 3#usize we20 (by decide)
                                          · intro a
                                            rfl
/-- Factor the original Pair source body at the exact term-prefix/tail cut. -/
def pairAfterLowFactored
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact) :
    Result (ControlFlow (PR × PW) PW) := do
  let p ← AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12
  pairAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- Candidate source body factored at the same cut; its suffix reuses the
fourth term-call's `perm3`. -/
def candidateAfterLowFactored
    (ap1 : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (side : PU) (iterNext : PR)
    (weights : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (q41 q8 q12 q16 : AspisR1S9CandidateHelperV1.field.QM31)
    (low : AspisR1S9CandidateHelperV1.field.WideExact) :
    Result (ControlFlow (PR × Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
      (Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))) := do
  let p ← AspisR1S9PairTermPrefixMapV1.candidateTermPrefix ap1 q41 q8 q12
  candidateAfterTermsBound ap1 side iterNext weights q41 q8 q12 q16 low
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- The factored Pair definition is exactly the emitted Pair continuation.
The only reassociation is the grouping of already-bound term results. -/
theorem pair_after_low_eq_factored
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact) :
    AspisR1S9PairCallerBodyPrefixV1.pairAfterLow ap1 side iterNext weights
      q41 q8 q12 q16 low =
      pairAfterLowFactored ap1 side iterNext weights q41 q8 q12 q16 low := by
  simp only [AspisR1S9PairCallerBodyPrefixV1.pairAfterLow, pairAfterLowFactored,
    AspisR1S9PairTermPrefixMapV1.pairTermPrefix,
    AspisR1S9PairTermPrefixMapV1.pairTermAt, pairAfterTerms, bind_assoc, bind_tc_ok]

/-- The factored Candidate definition retains the already-bound fourth
permutation value in the side-one suffix, exactly as its generated body does. -/
theorem candidate_after_low_eq_factored
    (ap1 : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (side : PU) (iterNext : PR)
    (weights : Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize))
    (q41 q8 q12 q16 : AspisR1S9CandidateHelperV1.field.QM31)
    (low : AspisR1S9CandidateHelperV1.field.WideExact) :
    AspisR1S9CandidateBodyPrefixV1.candidateAfterLow ap1 side iterNext weights
      q41 q8 q12 q16 low =
      candidateAfterLowFactored ap1 side iterNext weights q41 q8 q12 q16 low := by
  simp only [AspisR1S9CandidateBodyPrefixV1.candidateAfterLow,
    candidateAfterLowFactored, AspisR1S9PairTermPrefixMapV1.candidateTermPrefix,
    AspisR1S9PairTermPrefixMapV1.candidateTermAt,
    AspisR1S9CandidateBodyTermsV1.candidateHigh, candidateAfterTermsBound,
    bind_assoc, bind_tc_ok]

/-- The full suffix map is derived from the one term-prefix map followed by
its exact bound suffix map. -/
theorem pair_after_low_factored_result_maps
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact) :
    AspisR1S9PairCallerCandidateMapV1.mapResult pairMapFlow
      (pairAfterLowFactored ap1 side iterNext weights q41 q8 q12 q16 low) =
    candidateAfterLowFactored
      (mapArray pairToCandidateW ap1) side iterNext (mapArray pairToCandidateW weights)
      (pairToCandidateQ q41) (pairToCandidateQ q8) (pairToCandidateQ q12)
      (pairToCandidateQ q16) (pairToCandidateW low) := by
  unfold pairAfterLowFactored candidateAfterLowFactored
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (f := pairMapFlow) (g := AspisR1S9PairTermPrefixMapV1.mapPairPrefixResult)
  · exact AspisR1S9PairTermPrefixMapV1.pair_term_prefix_maps_to_candidate
      ap1 q41 q8 q12
  · intro p
    cases p with
    | mk perm3 tuple =>
      cases tuple with
      | mk t0 tuple =>
        cases tuple with
        | mk t1 tuple =>
          cases tuple with
          | mk t2 t3 =>
            exact pair_after_terms_bound_result_maps ap1 side iterNext weights
              q41 q8 q12 q16 low perm3 t0 t1 t2 t3


/-- Full Result-level Pair-to-Candidate map for the extracted post-scalar
source bodies. This retains failure/divergence and uses the same bound
`PERM[3]` result in both suffixes. -/
theorem pair_after_low_result_maps
    (ap1 : PW) (side : PU) (iterNext : PR) (weights : PW)
    (q41 q8 q12 q16 : PQ) (low : AspisR1S9PairCallerStepV1.field.WideExact) :
    AspisR1S9PairCallerCandidateMapV1.mapResult pairMapFlow
      (AspisR1S9PairCallerBodyPrefixV1.pairAfterLow ap1 side iterNext weights
        q41 q8 q12 q16 low) =
    AspisR1S9CandidateBodyPrefixV1.candidateAfterLow
      (mapArray pairToCandidateW ap1) side iterNext (mapArray pairToCandidateW weights)
      (pairToCandidateQ q41) (pairToCandidateQ q8) (pairToCandidateQ q12)
      (pairToCandidateQ q16) (pairToCandidateW low) := by
  rw [pair_after_low_eq_factored, candidate_after_low_eq_factored]
  exact pair_after_low_factored_result_maps ap1 side iterNext weights
    q41 q8 q12 q16 low

#print axioms pair_after_terms_bound_result_maps
#print axioms pair_after_low_eq_factored
#print axioms candidate_after_low_eq_factored
#print axioms pair_after_low_factored_result_maps
#print axioms pair_after_low_result_maps

end AspisR1S9PairCandidateAfterTermsMapV1
