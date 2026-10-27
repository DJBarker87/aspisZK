import R1Z.QueryScanRealLazyBound

/-! QueryScan observations on the ACTUAL headline parser. This module proves
Lean-model control preservation, not native Vec/contains execution refinement. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F5
open R0Z.FsStatement R1Z.PhaseSamplerParserBin R1Z.PhaseQueryScanBin
  AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

/-- Ordered contains comparisons, including the first equality if any. -/
def comparisons (x : Nat) : List Nat → List (Nat × Bool)
  | [] => []
  | y :: ys => (y, decide (x = y)) :: if x = y then [] else comparisons x ys

inductive Event where
  | exhausted (s : ScanState)
  | guard (s : ScanState) (stopped : Bool)
  | candidate (draw : Nat) (x : Nat) (tests : List (Nat × Bool)) (duplicate : Bool)
  deriving DecidableEq

/-- Mirrors scan's pre-word guard. In particular, the empty suffix does not
perform the guard and completion at a block boundary can read another block. -/
def scanHistory : ScanState → List Nat → List Event
  | s, [] => [.exhausted s]
  | s, x :: xs =>
    if s.accepted.length = 22 ∨ s.draws = 64 then [.guard s true]
    else .guard s false :: .candidate s.draws x (comparisons x s.accepted)
      (decide (x ∈ s.accepted)) :: scanHistory ⟨keep s.accepted x, s.draws + 1⟩ xs

/-- Instrumented executor, with the existing scan returned unchanged. -/
def instrumented (s : ScanState) (xs : List Nat) := (scan s xs, scanHistory s xs)

theorem instrumented_erases (s : ScanState) (xs : List Nat) :
    (instrumented s xs).1 = scan s xs := rfl

/-- Retains each block's parser state/history, first-stop index and finish
result. No successful-query-set quotient discards duplicate or failed words. -/
def history (q : Fin 8 → OracleAnswer) :=
  let k := stop done q
  (k, ((List.ofFn q).take (k.val + 1)),
    ((List.finRange 8).filter (fun j => decide (j ≤ k))).map (fun j =>
      (scanned j q, scanHistory AspisR1.QueryScanModelFailure.initial (parsedWords q j))),
    finish (scanned k q).1)

theorem history_prefix (q q' : Fin 8 → OracleAnswer)
    (he : PrefixAgree q q' (stop done q)) : history q = history q' := by
  have hs := stop_local done q q' he
  have hraw : (List.ofFn q).take ((stop done q).val + 1) =
      (List.ofFn q').take ((stop done q).val + 1) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
    · intro i hi hi'
      have hil := hi
      simp only [List.length_take, List.length_ofFn] at hil
      simp only [List.getElem_take, List.getElem_ofFn]
      exact he ⟨i, by omega⟩ (by change i ≤ (stop done q).val; omega)
  have hw (j : Fin 8) (hj : j ≤ stop done q) : parsedWords q j = parsedWords q' j := by
    unfold parsedWords
    have hh : (List.ofFn q).take (j.val + 1) = (List.ofFn q').take (j.val + 1) := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_ofFn]
      · intro i hi hi'
        have hil := hi
        simp only [List.length_take, List.length_ofFn] at hil
        simp only [List.getElem_take, List.getElem_ofFn]
        exact he ⟨i, by omega⟩ (by change i ≤ (stop done q).val; have := j.isLt; omega)
    rw [hh]
  unfold history
  rw [← hs]
  simp only [hraw]
  have hscan (j : Fin 8) (hj : j ≤ stop done q) : scanned j q = scanned j q' := by
    unfold scanned
    rw [hw j hj]
  rw [hscan _ (le_refl _)]
  congr 3
  apply List.map_congr_left
  intro i hi
  have hj : i ≤ stop done q := by
    have hm := (List.mem_filter.mp hi).2
    exact of_decide_eq_true hm
  rw [hscan _ hj, hw _ hj]

#print axioms instrumented_erases
#print axioms history_prefix
end R1Z.PV_L2_F5
