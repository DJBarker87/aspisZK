import V7ProductionCallbacksR30FromFnCanonical
import V7ProductionCallbacksR30QueryGammaCanonical
import V7ProductionCallbacksR30NormalizedFoldCanonical

/-! Canonicality through all sixteen literal source query-fold callbacks. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result

namespace V7ProductionCallbacksR30FoldQueriesCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30ArrayCanonical
open V7ProductionCallbacksR30FromFnCanonical
open V7ProductionCallbacksR30QueryGammaCanonical
open V7ProductionCallbacksR30NormalizedFoldCanonical
open V7CallerCurrentReleaseR26FieldBridge

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private abbrev QM31 := V7ProductionCallbacksR29.aspis_core.field.QM31
private abbrev Closure := V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries.closure
local instance : Inhabited QM31 := ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩
local instance : Inhabited Row := ⟨Array.repeat 4#usize V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩
private def ClosureCanonical (state : Closure) : Prop := RowsCanonical state.1

private theorem closure_preserves_canonical
    (state : Closure) (index : Std.Usize) (output : QM31) (next : Closure)
    (canonical : ClosureCanonical state)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      state index = ok (output, next)) :
    GeneratedCanonicalQM31 output ∧ ClosureCanonical next := by
  rcases state with ⟨combined, powers, coordinates⟩
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨row, rowRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inv2x, inv2xRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inv2y, inv2yRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨folded, foldedRun, run⟩ := run
  have rowCanonical := array_index_all RowCanonical combined index row canonical rowRun
  have foldedCanonical := successful_normalized_polynomial_refs_canonical
    row powers inv2x inv2y folded rowCanonical foldedRun
  have pairExact := Result.ok.inj run
  cases pairExact
  exact ⟨foldedCanonical, canonical⟩

theorem successful_fold_queries_canonical
    (combined : Array (Array QM31 4#usize) 16#usize)
    (coordinates : V7ProductionCallbacksR29.aspis_core.v6_onefold.V6OneFoldCoordinates)
    (alpha : QM31) (output : Array QM31 16#usize)
    (canonical : RowsCanonical combined)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries
      combined coordinates alpha = ok output) :
    SliceAll GeneratedCanonicalQM31 output.to_slice := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alphaSquared, squareRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨preparedAlpha, preparedAlphaRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨preparedSquared, preparedSquaredRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alphaCubed, cubedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨preparedCubed, preparedCubedRun, run⟩ := run
  exact from_fn_all
    V7ProductionCallbacksR29.aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    GeneratedCanonicalQM31 ClosureCanonical closure_preserves_canonical
    16#usize (combined, Array.make 3#usize [preparedAlpha, preparedSquared, preparedCubed], coordinates)
    output canonical run

#print axioms successful_fold_queries_canonical
end V7ProductionCallbacksR30FoldQueriesCanonical
