import AspisR1S9CandidateHelperV1.Funs
import AspisR1S9HelperP6.Funs
import S9CandidateHelperOperationBridgeV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateScalarFactorCallbackTransportV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CandidateClosure := AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor.closure
abbrev P6Closure := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure

def mapCandidateClosure (c : CandidateClosure) : P6Closure :=
  (mapArray toP6W c.1, mapArray toP6Q c.2)

def mapCandidateCallbackResult (z : CW × CandidateClosure) : PW × P6Closure :=
  (toP6W z.1, mapCandidateClosure z.2)

theorem mapResult_id {A : Type} (r : Result A) : mapResult id r = r := by
  cases r <;> rfl

/-- The real generated FnMut callback commutes with the carrier map through
all three indexed reads and both installed wide operations. Its equality
preserves fail/div branches and the returned closure. -/
theorem candidate_call_mut_maps (c : CandidateClosure) (v : CW) (i : Std.Usize) :
    mapResult mapCandidateCallbackResult
      (AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        c (v, i)) =
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (mapCandidateClosure c) (toP6W v, i) := by
  unfold AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
  change mapResult mapCandidateCallbackResult
      (do
        let (a, a1) := c
        let (v, s) := (v, i)
        let index ← Array.index_usize AspisR1S9CandidateHelperV1.weights.PERM s
        let wide ← Array.index_usize a index
        let q ← Array.index_usize a1 s
        let product ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 wide q
        let total ← AspisR1S9CandidateHelperV1.field.WideExact.add v product
        ok (total, c)) =
    (do
      let (a, a1) := mapCandidateClosure c
      let (v, s) := (toP6W v, i)
      let index ← Array.index_usize AspisR1S9HelperP6.weights.PERM s
      let wide ← Array.index_usize a index
      let q ← Array.index_usize a1 s
      let product ← AspisR1S9HelperP6.field.WideExact.mul_qm31 wide q
      let total ← AspisR1S9HelperP6.field.WideExact.add v product
      ok (total, (a, a1)))
  apply mapResult_bind_congr (f := mapCandidateCallbackResult) (g := id)
  · have hperm : AspisR1S9CandidateHelperV1.weights.PERM =
        AspisR1S9HelperP6.weights.PERM := by
      unfold AspisR1S9CandidateHelperV1.weights.PERM AspisR1S9HelperP6.weights.PERM
      rfl
    rw [hperm]
    exact mapResult_id _
  · intro index
    apply mapResult_bind_congr (f := mapCandidateCallbackResult) (g := toP6W)
    · exact mapArray_index_result toP6W c.1 index
    · intro wide
      apply mapResult_bind_congr (f := mapCandidateCallbackResult) (g := toP6Q)
      · exact mapArray_index_result toP6Q c.2 i
      · intro q
        apply mapResult_bind_congr (f := mapCandidateCallbackResult) (g := toP6W)
        · exact AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31 wide q
        · intro product
          apply mapResult_bind_congr (f := mapCandidateCallbackResult) (g := toP6W)
          · exact AspisR1S9CandidateHelperBridgeV1.map_wide_add v product
          · intro total
            rfl

#print axioms candidate_call_mut_maps

end AspisR1S9CandidateScalarFactorCallbackTransportV1
