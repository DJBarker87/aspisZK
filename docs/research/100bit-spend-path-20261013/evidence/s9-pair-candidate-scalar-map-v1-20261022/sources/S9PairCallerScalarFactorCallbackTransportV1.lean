import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9HelperP6.Funs
import S9PairCallerStepOperationBridgeV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerScalarFactorCallbackTransportV1

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapResult f

open AspisR1S9PairCallerStepV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev CQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PairClosure := AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure
abbrev P6Closure := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure

def mapPairClosure (c : PairClosure) : P6Closure :=
  (mapArray toP6W c.1, mapArray toP6Q c.2)

def mapPairCallbackResult (z : CW × PairClosure) : PW × P6Closure :=
  (toP6W z.1, mapPairClosure z.2)

theorem mapResult_id {A : Type} (r : Result A) : mapResult id r = r := by
  cases r <;> rfl

/-- The real generated FnMut callback commutes with the carrier map through
all three indexed reads and both installed wide operations. Its equality
preserves fail/div branches and the returned closure. -/
theorem pair_call_mut_maps (c : PairClosure) (v : CW) (i : Std.Usize) :
    mapResult mapPairCallbackResult
      (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        c (v, i)) =
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (mapPairClosure c) (toP6W v, i) := by
  unfold AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
  change mapResult mapPairCallbackResult
      (do
        let (a, a1) := c
        let (v, s) := (v, i)
        let index ← Array.index_usize AspisR1S9PairCallerStepV1.weights.PERM s
        let wide ← Array.index_usize a index
        let q ← Array.index_usize a1 s
        let product ← AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 wide q
        let total ← AspisR1S9PairCallerStepV1.field.WideExact.add v product
        ok (total, c)) =
    (do
      let (a, a1) := mapPairClosure c
      let (v, s) := (toP6W v, i)
      let index ← Array.index_usize AspisR1S9HelperP6.weights.PERM s
      let wide ← Array.index_usize a index
      let q ← Array.index_usize a1 s
      let product ← AspisR1S9HelperP6.field.WideExact.mul_qm31 wide q
      let total ← AspisR1S9HelperP6.field.WideExact.add v product
      ok (total, (a, a1)))
  apply mapResult_bind_congr (f := mapPairCallbackResult) (g := id)
  · have hperm : AspisR1S9PairCallerStepV1.weights.PERM =
        AspisR1S9HelperP6.weights.PERM := by
      unfold AspisR1S9PairCallerStepV1.weights.PERM AspisR1S9HelperP6.weights.PERM
      rfl
    rw [hperm]
    exact mapResult_id _
  · intro index
    apply mapResult_bind_congr (f := mapPairCallbackResult) (g := toP6W)
    · exact mapArray_index_result toP6W c.1 index
    · intro wide
      apply mapResult_bind_congr (f := mapPairCallbackResult) (g := toP6Q)
      · exact mapArray_index_result toP6Q c.2 i
      · intro q
        apply mapResult_bind_congr (f := mapPairCallbackResult) (g := toP6W)
        · exact AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_qm31 wide q
        · intro product
          apply mapResult_bind_congr (f := mapPairCallbackResult) (g := toP6W)
          · exact AspisR1S9PairCallerStepOperationBridgeV1.map_wide_add v product
          · intro total
            rfl

#print axioms pair_call_mut_maps

end AspisR1S9PairCallerScalarFactorCallbackTransportV1
