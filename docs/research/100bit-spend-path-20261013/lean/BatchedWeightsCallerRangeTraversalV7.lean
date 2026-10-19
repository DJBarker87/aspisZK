import BatchedWeightsCallerSafeCadenceV4
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsCallerRangeTraversalV1
open BatchedWeightsCallerSafeCadenceV4

abbrev BW := BatchedWeightsCallerSafeCadenceV4.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsCallerSafeCadenceV4.Q
abbrev M := BatchedWeightsCallerSafeCadenceV4.M

/-- Source-shaped ascending index traversal for the caller's `0..len()` loop.
The caller-specific power and basis projections remain explicit functions. -/
def rangeVisits (n : Nat) (indexAt : Nat → Usize)
    (powerAt : Nat → Q) (basisAt : Nat → M) : List RowVisit :=
  (List.range n).map fun i =>
    { index := indexAt i, power := powerAt i, basis := basisAt i }

theorem rangeVisits_indices_nodup
    (n : Nat) (indexAt : Nat → Usize) (powerAt : Nat → Q) (basisAt : Nat → M)
    (hindex : ∀ i, i < n → (indexAt i).val = i) :
    ((rangeVisits n indexAt powerAt basisAt).map fun v => v.index.val).Nodup := by
  have hmap : (rangeVisits n indexAt powerAt basisAt).map (fun v => v.index.val) =
      List.range n := by
    unfold rangeVisits
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (List.range n)]
    apply List.map_congr_left
    intro i hi
    exact hindex i (List.mem_range.mp hi)
  rw [hmap]
  exact List.nodup_range

/-- If each source position has a valid index, canonical operands and a raw
phase bound, the ascending row list satisfies the per-visit contract consumed
by the selected-push caller theorem. -/
theorem rangeVisits_safe
    (n : Nat) (state : BW) (indexAt : Nat → Usize)
    (powerAt : Nat → Q) (basisAt : Nat → M)
    (hlen : n ≤ state.raw.val.length)
    (hindex : ∀ i, i < n → (indexAt i).val = i)
    (hraw : ∀ (i : Nat) (hi : i < n) (k : Usize) (hk : k.val < 4),
      AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt state (indexAt i)
        (by rw [hindex i hi]; exact Nat.lt_of_lt_of_le hi hlen) k hk <
        2^34 + state.terms.val % 4 * AspisR1BatchedAllPrefix.cap)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P) :
    VisitsSafe (rangeVisits n indexAt powerAt basisAt) state := by
  intro visit hvisit
  rcases List.mem_map.mp hvisit with ⟨i, hi, heq⟩
  have hin : i < n := List.mem_range.mp hi
  subst visit
  have hvalid : (indexAt i).val < state.raw.length := by
    change (indexAt i).val < state.raw.val.length
    rw [hindex i hin]
    exact Nat.lt_of_lt_of_le hin hlen
  refine ⟨hvalid, ?_, hpower0a i hin, hpower0b i hin,
    hpower1a i hin, hpower1b i hin, hbasis i hin⟩
  intro k hk
  exact hraw i hin k hk

theorem rangeVisits_safeRows
    (n : Nat) (state : BW) (indexAt : Nat → Usize)
    (powerAt : Nat → Q) (basisAt : Nat → M)
    (hlen : n ≤ state.raw.val.length)
    (hindex : ∀ i, i < n → (indexAt i).val = i)
    (hraw : ∀ (i : Nat) (hi : i < n) (k : Usize) (hk : k.val < 4),
      AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt state (indexAt i)
        (by rw [hindex i hi]; exact Nat.lt_of_lt_of_le hi hlen) k hk <
        2^34 + state.terms.val % 4 * AspisR1BatchedAllPrefix.cap)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P) :
    ∃ final, SafeRows (rangeVisits n indexAt powerAt basisAt) state final := by
  apply safeRows_of_distinct_visits
  · exact rangeVisits_indices_nodup n indexAt powerAt basisAt hindex
  · exact rangeVisits_safe n state indexAt powerAt basisAt hlen hindex hraw
      hpower0a hpower0b hpower1a hpower1b hbasis

#print axioms rangeVisits_indices_nodup
#print axioms rangeVisits_safe
#print axioms rangeVisits_safeRows
end BatchedWeightsCallerRangeTraversalV1
