import SelectedValueAuxiliarySourcePolynomial

/-! Exact selected reverse-Horner recomposition source.

The pinned Rust evaluates each ten-bit view by folding bits 8 down to 0 from
seed bit 9, then combines current/successor/XOR12 views with scales
1, 2^10, and 2^20.  This leaf proves that exact order equals the intended
little-endian linear combination, builds its one-coordinate polynomial
slice, and constructs the chronological source object. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 2500

namespace AspisV8Completion.SelectedRecompositionSourcePolynomial
open scoped BigOperators
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedAmountEndpoint
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.SelectedRangeOutputsSourcePolynomial
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial

abbrev K := QM31Exact
abbrev F := M31Exact

def sourceHornerK (f : Nat → K) (n : Nat) (seed : K) : K :=
  ((List.range n).reverse).foldl (fun acc i => acc + acc + f i) seed

theorem sourceHornerK_succ (f : Nat → K) (n : Nat) (seed : K) :
    sourceHornerK f (n + 1) seed =
      sourceHornerK f n (seed + seed + f n) := by
  simp only [sourceHornerK, List.range_succ, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.foldl_cons]

theorem sourceHornerK_sum (f : Nat → K) (n : Nat) (seed : K) :
    sourceHornerK f n seed =
      (∑ i ∈ Finset.range n, f i * (2 : K) ^ i) + seed * (2 : K) ^ n := by
  induction n generalizing seed with
  | zero => simp [sourceHornerK]
  | succ n ih =>
    rw [sourceHornerK_succ, ih, Finset.sum_range_succ, pow_succ]
    ring

/-- Literal Rust order: `view[..9].iter().rev().fold(view[9], ...)`. -/
def reverseHorner10 (view : Fin 10 → K) : K :=
  sourceHornerK (fun i => view ⟨i % 10, Nat.mod_lt _ (by decide)⟩) 9 (view 9)

theorem reverseHorner10_eq_sum (view : Fin 10 → K) :
    reverseHorner10 view = ∑ bit : Fin 10, view bit * (2 : K) ^ bit.val := by
  rw [reverseHorner10, sourceHornerK_sum]
  have combined :
      (∑ i ∈ Finset.range 9,
        view ⟨i % 10, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i) +
          view 9 * (2 : K) ^ 9 =
        ∑ i ∈ Finset.range 10,
          view ⟨i % 10, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i :=
    (Finset.sum_range_succ (fun i =>
      view ⟨i % 10, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i) 9).symm
  rw [combined, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro bit _
  simp only [Nat.mod_eq_of_lt bit.isLt]

def openedView (table : BaseTable) (point : Fin 10 → K) (view : Fin 3) :
    Fin 10 → K := fun bit =>
  tableMLEValue point (traceTable table view bit.val)

def literalReconstruction (table : BaseTable) (point : Fin 10 → K) : K :=
  reverseHorner10 (openedView table point 0) +
    reverseHorner10 (openedView table point 1) * (2 : K) ^ 10 +
    reverseHorner10 (openedView table point 2) * (2 : K) ^ 20

def linearView (table : BaseTable) (point : Fin 10 → K) (view : Fin 3) : K :=
  ∑ bit : Fin 10,
    tableMLEValue point (traceTable table view bit.val) * (2 : K) ^ bit.val

def linearReconstruction (table : BaseTable) (point : Fin 10 → K) : K :=
  linearView table point 0 +
    linearView table point 1 * (2 : K) ^ 10 +
    linearView table point 2 * (2 : K) ^ 20

theorem reverseHorner_opened_eq_linearView (table : BaseTable)
    (point : Fin 10 → K) (view : Fin 3) :
    reverseHorner10 (openedView table point view) = linearView table point view := by
  rw [reverseHorner10_eq_sum]
  rfl

theorem literalReconstruction_eq_linear (table : BaseTable) (point : Fin 10 → K) :
    literalReconstruction table point = linearReconstruction table point := by
  unfold literalReconstruction linearReconstruction
  rw [reverseHorner_opened_eq_linearView,
    reverseHorner_opened_eq_linearView,
    reverseHorner_opened_eq_linearView]

noncomputable def linearViewSlice (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) : K[X] :=
  ∑ bit : Fin 10,
    C ((2 : K) ^ bit.val) *
      openingSlice (traceTable table view bit.val) fixed round

theorem linearViewSlice_degree (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (linearViewSlice table view fixed round).natDegree ≤ 1 := by
  unfold linearViewSlice
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro bit _
  exact (natDegree_C_mul_le _ _).trans
    (openingSlice_degree (traceTable table view bit.val) fixed round)

theorem linearViewSlice_eval_at (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    (linearViewSlice table view fixed round).eval x =
      linearView table (replaceCoordinate fixed round x) view := by
  simp only [linearViewSlice, linearView, Polynomial.eval_finsetSum,
    eval_mul, eval_C, openingSlice_eval_at]
  apply Finset.sum_congr rfl
  intro bit _
  ring

noncomputable def linearReconstructionSlice (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) : K[X] :=
  linearViewSlice table 0 fixed round +
    C ((2 : K) ^ 10) * linearViewSlice table 1 fixed round +
    C ((2 : K) ^ 20) * linearViewSlice table 2 fixed round

theorem linearReconstructionSlice_degree (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (linearReconstructionSlice table fixed round).natDegree ≤ 1 := by
  unfold linearReconstructionSlice
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le
      (linearViewSlice_degree table 0 fixed round)
      ((natDegree_C_mul_le _ _).trans
        (linearViewSlice_degree table 1 fixed round))))
    ((natDegree_C_mul_le _ _).trans
      (linearViewSlice_degree table 2 fixed round)))

theorem linearReconstructionSlice_eval_at (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    (linearReconstructionSlice table fixed round).eval x =
      linearReconstruction table (replaceCoordinate fixed round x) := by
  unfold linearReconstructionSlice linearReconstruction
  rw [eval_add, eval_add, eval_mul, eval_mul, eval_C, eval_C,
    linearViewSlice_eval_at, linearViewSlice_eval_at,
    linearViewSlice_eval_at]
  ring

noncomputable def recompositionSpec (table : BaseTable) :
    CoordinateSlices (K := K) where
  value := fun point => rangeSelectorValue point *
    (tableMLEValue point (traceTable table 0 10) - literalReconstruction table point)
  slice := fun fixed round => rangeSelectorSlice fixed round *
    (openingSlice (traceTable table 0 10) fixed round -
      linearReconstructionSlice table fixed round)
  degree := by
    intro fixed round
    apply natDegree_mul_le.trans
    exact (Nat.add_le_add (rangeSelectorSlice_degree fixed round)
      ((natDegree_sub_le _ _).trans (max_le
        (openingSlice_degree (traceTable table 0 10) fixed round)
        (linearReconstructionSlice_degree table fixed round)))).trans (by omega)
  eval_at := by
    intro fixed round x
    simp only [eval_mul, eval_sub, rangeSelectorSlice_eval_at,
      openingSlice_eval_at, linearReconstructionSlice_eval_at]
    rw [literalReconstruction_eq_linear]

theorem recompositionSpec_value (table : BaseTable) (point : Fin 10 → K) :
    (recompositionSpec table).value point =
      rangeSelectorValue point *
        (tableMLEValue point (traceTable table 0 10) -
          literalReconstruction table point) := rfl

noncomputable def source (table : BaseTable) :
    SourcePolynomial (booleanTable (recompositionSpec table)) :=
  BooleanSuffixSourceConstructor.source (recompositionSpec table)

theorem tenAt_eq_sum (table : BaseTable) (row : Nat) :
    tenAt table row = ∑ bit : Fin 10, table row bit.val * (2 : F) ^ bit.val := by
  rw [tenAt, sourceHorner_sum]
  have combined :
      (∑ i ∈ Finset.range 9, table row i * (2 : F) ^ i) +
          table row 9 * (2 : F) ^ 9 =
        ∑ i ∈ Finset.range 10, table row i * (2 : F) ^ i :=
    (Finset.sum_range_succ (fun i => table row i * (2 : F) ^ i) 9).symm
  rw [combined, Finset.sum_range]

theorem liftBase_pow_two (n : Nat) : liftBase ((2 : F) ^ n) = (2 : K) ^ n := by
  induction n with
  | zero => simp [liftBase_one]
  | succ n ih =>
    rw [pow_succ, liftBase_mul, ih, pow_succ]
    rfl

theorem liftBase_finsetSum {I : Type*} (set : Finset I) (f : I → F) :
    liftBase (∑ i ∈ set, f i) = ∑ i ∈ set, liftBase (f i) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [liftBase_zero]
  | @insert item set absent ih =>
    simp only [Finset.sum_insert absent, ih, liftBase_add]

theorem linearView_boolean (table : BaseTable) (row : Fin 1024) (view : Fin 3) :
    linearView table (booleanTracePoint row) view =
      liftBase (tenAt table (viewRow row.val view)) := by
  rw [tenAt_eq_sum]
  unfold linearView
  rw [liftBase_finsetSum]
  apply Finset.sum_congr rfl
  intro bit _
  rw [traceTable_boolean, liftBase_mul, liftBase_pow_two]

theorem linearReconstruction_boolean (table : BaseTable) (row : Fin 1024) :
    linearReconstruction table (booleanTracePoint row) =
      liftBase (reconstructAt table row.val) := by
  unfold linearReconstruction
  rw [linearView_boolean, linearView_boolean, linearView_boolean]
  rw [reconstructAt_source]
  rw [liftBase_add, liftBase_add, liftBase_mul, liftBase_mul,
    liftBase_pow_two, liftBase_pow_two]
  simp [viewRow]

theorem booleanTable_eq_literal_recomposition (pub : Public) (table : BaseTable)
    (row : Fin 1024) :
    booleanTable (recompositionSpec table) row =
      liftBase (AspisV8.SelectedSemanticRows.residual pub table
        .recomposition row.val) := by
  unfold booleanTable
  rw [recompositionSpec_value]
  rw [rangeSelectorValue_booleanTracePoint, traceTable_boolean,
    literalReconstruction_eq_linear, linearReconstruction_boolean]
  change (if valueMask row.val then 1 else 0) *
      (liftBase (table row.val 10) - liftBase (reconstructAt table row.val)) =
    liftBase (if valueMask row.val then table row.val 10 - reconstructAt table row.val else 0)
  by_cases active : valueMask row.val
  · simp [active, liftBase_sub]
  · simp [active, liftBase_zero]

theorem source_initial_is_literal_recomposition (pub : Public) (table : BaseTable) :
    ((source table).restriction 0 []).eval 0 +
        ((source table).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, liftBase (AspisV8.SelectedSemanticRows.residual pub table
        .recomposition row.val) := by
  rw [(source table).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_recomposition pub table row

#print axioms sourceHornerK_sum
#print axioms reverseHorner10_eq_sum
#print axioms literalReconstruction_eq_linear
#print axioms linearViewSlice_degree
#print axioms linearViewSlice_eval_at
#print axioms linearReconstructionSlice_degree
#print axioms linearReconstructionSlice_eval_at
#print axioms recompositionSpec
#print axioms linearReconstruction_boolean
#print axioms booleanTable_eq_literal_recomposition
#print axioms source
#print axioms source_initial_is_literal_recomposition
end AspisV8Completion.SelectedRecompositionSourcePolynomial
