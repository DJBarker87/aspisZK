import BatchedWeightsCallerSafeCadenceV4
import BatchedWeightsCallerRangeTraversalV7
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open AspisR1BatchedWeightsExtraction

namespace BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsCallerSafeCadenceV4
open BatchedWeightsCallerRangeTraversalV1
abbrev BW := BatchedWeightsCallerSafeCadenceV4.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsCallerSafeCadenceV4.Q
abbrev M := BatchedWeightsCallerSafeCadenceV4.M

def readPushRows (basis : Slice M) (powerAt : Usize → Q) :
    List Usize → BW → Result BW
  | [], state => .ok state
  | index :: rest, state => do
      let basisValue ← Slice.index_usize basis index
      let state' ← batched_weights.BatchedWeights.push state index
        (powerAt index) basisValue
      readPushRows basis powerAt rest state'

def projectedRows (basisAt : Usize → M) (powerAt : Usize → Q) :
    List Usize → List RowVisit
  | [] => []
  | index :: rest =>
      { index := index, power := powerAt index, basis := basisAt index } ::
        projectedRows basisAt powerAt rest

def readPushQuery (basis : Slice M)
    (powerAt : Usize → Q) (indices : List Usize) (state : BW) : Result BW := do
  let afterRows ← readPushRows basis powerAt indices state
  let nextTerms ← afterRows.terms + 1#usize
  ok { afterRows with terms := nextTerms }

theorem readPushRows_eq_pushRows
    (basis : Slice M) (basisAt : Usize → M) (powerAt : Usize → Q)
    (indices : List Usize)
    (hread : ∀ i, i ∈ indices → Slice.index_usize basis i = .ok (basisAt i))
    (state : BW) :
    readPushRows basis powerAt indices state =
      pushRows (projectedRows basisAt powerAt indices) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      have hr := hread index (by simp)
      simp only [readPushRows, hr, bind_tc_ok, projectedRows, pushRows]
      apply bind_congr
      intro state'
      exact ih (by
        intro i hi
        exact hread i (by simp [hi])) state'

/-- The loop body uses the exact extracted slice read and row push operations.
Successful reads identify it with the checked `pushRows`/single-counter-step
query shell. This is the indexed source-shaped model for the isolated Rust
`push_query` helper; extraction identity remains a separate pending check. -/
theorem readPushQuery_eq_queryStep
    (basis : Slice M) (basisAt : Usize → M) (powerAt : Usize → Q)
    (indices : List Usize)
    (hread : ∀ i, i ∈ indices → Slice.index_usize basis i = .ok (basisAt i))
    (state : BW) :
    readPushQuery basis powerAt indices state =
      queryStep (projectedRows basisAt powerAt indices) state := by
  unfold readPushQuery queryStep
  rw [readPushRows_eq_pushRows basis basisAt powerAt indices hread state]
  rfl

theorem checked_cursor_increment
    (cursor next : Usize)
    (hroom : cursor.val + 1 ≤ Usize.max)
    (hadd : (cursor + 1#usize : Result Usize) = .ok next) :
    next.val = cursor.val + 1 := by
  have hspec : UScalar.add cursor 1#usize ⦃ z => z.val = cursor.val + 1 ⦄ := by
    apply UScalar.add_spec
    have hsum : cursor.val + (1#usize).val ≤ Usize.max := by simpa using hroom
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨result, hresult, hval⟩ := WP.spec_imp_exists hspec
  have heq : result = next := Result.ok.inj (hresult.symm.trans hadd)
  simpa [heq] using hval

def rangeCursor (i : Nat) : Usize :=
  UScalar.ofNatCore (i % 2^UScalarTy.Usize.numBits)
    (Nat.mod_lt i (by exact Nat.pow_pos (by omega : 0 < 2)))

theorem rangeCursor_val (i : Nat) (hi : i < 2^UScalarTy.Usize.numBits) :
    (rangeCursor i).val = i := by
  simp only [rangeCursor, UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt hi

/-- The `0..len` counter represented by `rangeCursor` is exactly the result of
the source's checked `j + 1` after each in-range iteration. -/
theorem rangeCursor_checked_step (i : Nat)
    (hi : i + 1 < 2^UScalarTy.Usize.numBits)
    (hroom : i + 1 ≤ Usize.max) :
    ∃ next : Usize,
      (rangeCursor i + 1#usize : Result Usize) = .ok next ∧
      next = rangeCursor (i + 1) := by
  have hcur := rangeCursor_val i (by omega)
  have hnext := rangeCursor_val (i + 1) hi
  have hone : (1#usize).val = 1 := by decide
  have hsum : (rangeCursor i).val + (1#usize).val ≤ Usize.max := by
    simpa [hcur, hone] using hroom
  have hchecked : UScalar.add (rangeCursor i) 1#usize
      ⦃ z => z.val = (rangeCursor i).val + (1#usize).val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨next, hadd, hval⟩ := WP.spec_imp_exists hchecked
  have hresult : (rangeCursor i + 1#usize : Result Usize) = .ok next := hadd
  have hnextVal : next.val = (rangeCursor (i + 1)).val := by
    rw [hval, hcur, hone, hnext]
  exact ⟨next, hresult, UScalar.eq_of_val_eq hnextVal⟩

def sliceCell (basis : Slice M) (i : Usize) (hi : i.val < basis.length) : M :=
  (↑basis)[↑i]

theorem slice_read_actual (basis : Slice M) (i : Usize)
    (hi : i.val < basis.length) :
    Slice.index_usize basis i = .ok (sliceCell basis i hi) := by
  have hbound : i.val < basis.length := by simpa using hi
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec basis i hbound)
  exact hx.trans (congrArg Result.ok (by simpa [sliceCell] using hval))

def rangeCursorList (n : Nat) : List Usize := (List.range n).map rangeCursor

def sliceBasisAt (basis : Slice M) (i : Usize) : M :=
  if h : i.val < basis.length then sliceCell basis i h else 0#u32

def natPowerAt (powerAt : Nat → Q) (i : Usize) : Q := powerAt i.val

private theorem projectedRows_eq_map (basisAt : Usize → M) (powerAt : Usize → Q)
    (indices : List Usize) :
    projectedRows basisAt powerAt indices =
      indices.map (fun i => { index := i, power := powerAt i, basis := basisAt i }) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [projectedRows, ih]

theorem expectedRangeRows_eq
    (basis : Slice M) (basisAt : Nat → M) (powerAt : Nat → Q)
    (n : Nat) (hn : n < 2^UScalarTy.Usize.numBits)
    (hlen : n ≤ basis.length)
    (hbase : ∀ i, i < n → basisAt i = sliceBasisAt basis (rangeCursor i)) :
    projectedRows (sliceBasisAt basis) (natPowerAt powerAt) (rangeCursorList n) =
      rangeVisits n rangeCursor powerAt basisAt := by
  rw [projectedRows_eq_map]
  unfold rangeCursorList rangeVisits
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  have hcursor := rangeCursor_val i (by omega)
  have hbound : (rangeCursor i).val < basis.length := by omega
  simp [natPowerAt, hcursor, hbound, hbase i hin]

/-- The finite source-shaped while-loop candidate on the actual ascending
`0..len` indices refines the already checked natural-range shell. The slice
projection is obtained from real `Slice.index_usize` reads, each `j+1` is
covered by `rangeCursor_checked_step`, every row uses extracted `push`, and
the single terms increment is the checked `queryStep` operation. This remains
a model until Aeneas validates the isolated Rust helper's generated body. -/
theorem indexed_range_query_eq_source_shell
    (basis : Slice M) (basisAt : Nat → M) (powerAt : Nat → Q)
    (n : Nat) (hn : n < 2^UScalarTy.Usize.numBits)
    (hlen : n ≤ basis.length)
    (hbase : ∀ i, i < n → basisAt i = sliceBasisAt basis (rangeCursor i))
    (state : BW) :
    readPushQuery basis (natPowerAt powerAt) (rangeCursorList n) state =
      queryStep (rangeVisits n rangeCursor powerAt basisAt) state := by
  have hread : ∀ i, i ∈ rangeCursorList n →
      Slice.index_usize basis i = .ok (sliceBasisAt basis i) := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨k, hk, heq⟩
    subst i
    have hklt : k < n := List.mem_range.mp hk
    have hcursor := rangeCursor_val k (by omega)
    have hbound : (rangeCursor k).val < basis.length := by omega
    simpa [sliceBasisAt, hbound] using slice_read_actual basis (rangeCursor k) hbound
  rw [readPushQuery_eq_queryStep basis (sliceBasisAt basis)
    (natPowerAt powerAt) (rangeCursorList n) hread state]
  rw [expectedRangeRows_eq basis basisAt powerAt n hn hlen hbase]


/-- Every cursor used by the ascending list admits the exact checked
successor used by the source loop. -/
theorem rangeCursorList_checked_steps (n : Nat)
    (hn : n < 2^UScalarTy.Usize.numBits) :
    ∀ i, i ∈ rangeCursorList n →
      ∃ next : Usize,
        (i + 1#usize : Result Usize) = .ok next ∧
        ∃ k, k < n ∧ i = rangeCursor k ∧ next = rangeCursor (k + 1) := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨k, hk, heq⟩
  subst i
  have hklt : k < n := List.mem_range.mp hk
  have hmax : Usize.max + 1 = 2^UScalarTy.Usize.numBits := by
    exact Usize.max_succ_eq_pow
  have hroom : k + 1 ≤ Usize.max := by omega
  obtain ⟨next, hstep, hnext⟩ := rangeCursor_checked_step k (by omega) hroom
  exact ⟨next, hstep, k, hklt, rfl, hnext⟩

/-- A direct specialization with the slice itself supplying each basis value;
no separate basis adapter remains in the premise. -/
theorem indexed_range_query_actual_slice
    (basis : Slice M) (powerAt : Nat → Q)
    (n : Nat) (hn : n < 2^UScalarTy.Usize.numBits)
    (hlen : n ≤ basis.length) (state : BW) :
    readPushQuery basis (natPowerAt powerAt) (rangeCursorList n) state =
      queryStep
        (rangeVisits n rangeCursor powerAt
          (fun i => sliceBasisAt basis (rangeCursor i))) state := by
  exact indexed_range_query_eq_source_shell basis
    (fun i => sliceBasisAt basis (rangeCursor i)) powerAt n hn hlen
    (by intro i hi; rfl) state

#print axioms readPushQuery_eq_queryStep
#print axioms readPushRows_eq_pushRows
#print axioms checked_cursor_increment
#print axioms rangeCursor_checked_step
#print axioms slice_read_actual
#print axioms expectedRangeRows_eq
#print axioms indexed_range_query_eq_source_shell
#print axioms rangeCursorList_checked_steps
#print axioms indexed_range_query_actual_slice
end BatchedWeightsIndexedQueryLoopModelV2
