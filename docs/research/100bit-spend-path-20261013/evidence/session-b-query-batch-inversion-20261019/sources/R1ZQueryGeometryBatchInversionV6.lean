import AspisFormal.CircleGroupOrder
import R1ZQueryGeometryBatchInversionV3

set_option autoImplicit false

namespace R1ZQueryGeometryBatchInversionV2

open AspisCircleGroupOrder
open R1ZQueryGeometryValuesV1
open R1ZQueryGeometryBatchInversionV1
open R1ZBatchInverseAlgebraV3
open R1ZBatchInverseSourceModelV1

structure QueryInput where
  px : ZMod P
  py : ZMod P
  parent : Fin 65536

def queryChunk (q : QueryInput) : List (ZMod P) :=
  oneQueryValues q.px q.py q.parent

def flattenQueryChunks (qs : List QueryInput) : List (ZMod P) :=
  (qs.map queryChunk).flatten

theorem queryChunk_entries_nonzero (q : QueryInput)
    (hq : ∀ i : Fin 5, queryGeometryValues q.px q.py q.parent i ≠ 0) :
    ∀ x, x ∈ queryChunk q → x ≠ 0 := by
  intro x hx
  rw [queryChunk, oneQueryValues, List.mem_ofFn] at hx
  rcases hx with ⟨i, hi⟩
  subst x
  exact hq i

theorem flattenQueryChunks_entries_nonzero (qs : List QueryInput)
    (hqs : ∀ q, q ∈ qs → ∀ i : Fin 5,
      queryGeometryValues q.px q.py q.parent i ≠ 0) :
    ∀ x, x ∈ flattenQueryChunks qs → x ≠ 0 := by
  induction qs with
  | nil => simp [flattenQueryChunks]
  | cons q qs ih =>
    intro x hx
    simp only [flattenQueryChunks, List.map_cons, List.flatten_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact queryChunk_entries_nonzero q (hqs q (by simp)) x hx
    · apply ih (by
        intro q' hq' i
        exact hqs q' (by simp [hq']) i) x hx

theorem query_range_batch_inverse (qs : List QueryInput)
    (hqs : ∀ q, q ∈ qs → ∀ i : Fin 5,
      queryGeometryValues q.px q.py q.parent i ≠ 0) :
    backwardsStored (flattenQueryChunks qs)
      (prefixRun (flattenQueryChunks qs) 1)
      (flattenQueryChunks qs).length
      ((flattenQueryChunks qs).prod⁻¹) =
      (flattenQueryChunks qs).map Inv.inv := by
  apply source_batch_inverse_model
  intro i hi
  exact flattenQueryChunks_entries_nonzero qs hqs _ (List.getElem_mem hi)


theorem nonzero_of_any_zero_false {α : Type*} [Zero α] [DecidableEq α] (xs : List α)
    (hzero : xs.any (fun x => decide (x = 0)) = false) :
    ∀ i (hi : i < xs.length), xs[i]'hi ≠ 0 := by
  intro i hi hx
  have hm : xs[i]'hi ∈ xs := List.getElem_mem hi
  have hany : xs.any (fun x => decide (x = 0)) = true := by
    apply List.any_eq_true.mpr
    exact ⟨xs[i]'hi, hm, by simp [hx]⟩
  rw [hzero] at hany
  contradiction

theorem query_range_batch_inverse_of_zero_test (qs : List QueryInput)
    (hzero : (flattenQueryChunks qs).any (fun x => decide (x = 0)) = false) :
    backwardsStored (flattenQueryChunks qs)
      (prefixRun (flattenQueryChunks qs) 1)
      (flattenQueryChunks qs).length
      ((flattenQueryChunks qs).prod⁻¹) =
      (flattenQueryChunks qs).map Inv.inv := by
  apply source_batch_inverse_model
  exact nonzero_of_any_zero_false _ hzero

/-- The source slice `queries[start..end]` represented as a list drop/take,
then mapped to the five ordered denominator slots for each query. -/
def rangeQueries (queries : List (Fin 262144)) (start stop : Nat) : List (Fin 262144) :=
  (queries.drop start).take (stop - start)

def rangeQueryInputs (point : Fin 262144 → ZMod P × ZMod P)
    (queries : List (Fin 262144)) (start stop : Nat) : List QueryInput :=
  (rangeQueries queries start stop).map (fun u =>
    ⟨(point u).1, (point u).2, sourceParent u⟩)

def rangeGeometryFlat (point : Fin 262144 → ZMod P × ZMod P)
    (queries : List (Fin 262144)) (start stop : Nat) : List (ZMod P) :=
  flattenQueryChunks (rangeQueryInputs point queries start stop)

theorem range_geometry_batch_inverse (point : Fin 262144 → ZMod P × ZMod P)
    (queries : List (Fin 262144)) (start stop : Nat)
    (hzero : (rangeGeometryFlat point queries start stop).any
      (fun x => decide (x = 0)) = false) :
    backwardsStored (rangeGeometryFlat point queries start stop)
      (prefixRun (rangeGeometryFlat point queries start stop) 1)
      (rangeGeometryFlat point queries start stop).length
      ((rangeGeometryFlat point queries start stop).prod⁻¹) =
      (rangeGeometryFlat point queries start stop).map Inv.inv := by
  exact query_range_batch_inverse_of_zero_test
    (rangeQueryInputs point queries start stop) hzero

#print axioms nonzero_of_any_zero_false
#print axioms range_geometry_batch_inverse
#print axioms flattenQueryChunks_entries_nonzero
#print axioms query_range_batch_inverse

end R1ZQueryGeometryBatchInversionV2
