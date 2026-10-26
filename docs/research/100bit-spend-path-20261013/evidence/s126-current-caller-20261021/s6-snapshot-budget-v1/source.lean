import S6SdkDependencyFactorV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SnapshotBudget
open AspisR1.S2W_D189Wrappers AspisR1.S2W_D189Entry

/-- Requested-byte reference for the EXISTING private Allocator interface.
It is not asserted to be the deployed bump allocator or to account for layout,
alignment, metadata Vecs, child Boxes or other omitted requests. -/
def budget : Allocator Nat where
  allocate := fun remaining bytes => if bytes ≤ remaining then ok (remaining-bytes) else fail .panic
  cleanup := fun remaining => ok remaining

/-- Exact source interface requests, including rejected buffer widths and
arbitrary complete Entry/handle/buffer carriers. No accepted call is assumed. -/
theorem first_snapshot_sum_bound (e : Entry) :
    (admittedSizes e 3 firstSizes).sum ≤ 61943 := by
  by_cases h0 : (e.buffers (e.handles 0).1).val.length = 58295
  all_goals by_cases h1 : (e.buffers (e.handles 1).1).val.length = 1880
  all_goals by_cases h2 : (e.buffers (e.handles 2).1).val.length = 1768
  all_goals simp [admittedSizes,firstSizes,List.range_succ,h0,h1,h2]

/-- Complete finite reservation is TOTAL and returns the exact remaining byte
budget whenever all requested bytes fit. -/
theorem reserve_fits (sizes : List Nat) (remaining : Nat)
    (fits : sizes.sum ≤ remaining) :
    reserve budget sizes remaining = ok (remaining-sizes.sum) := by
  induction sizes generalizing remaining with
  | nil => rfl
  | cons size rest ih =>
    have front : size ≤ remaining := by simp only [List.sum_cons] at fits;omega
    have tail : rest.sum ≤ remaining-size := by simp only [List.sum_cons] at fits;omega
    simp only [reserve,budget,front,if_pos,AspisR1.S2W_Trace.thenResult]
    rw [ih _ tail]
    congr 1
    simp only [List.sum_cons]
    omega

/-- The same interface records an abort when the total request exceeds budget.
This is a countermodel to inferring child headroom from snapshot success alone,
not a counterexample against the actual fresh release heap. -/
theorem reserve_insufficient (sizes : List Nat) (remaining : Nat)
    (short : remaining < sizes.sum) :
    reserve budget sizes remaining = fail .panic := by
  induction sizes generalizing remaining with
  | nil => simp only [List.sum_nil] at short;omega
  | cons size rest ih =>
    by_cases front : size ≤ remaining
    · have tail : remaining-size < rest.sum := by simp only [List.sum_cons] at short;omega
      simp only [reserve,budget,front,if_pos,AspisR1.S2W_Trace.thenResult]
      exact ih _ tail
    · simp [reserve,budget,front,AspisR1.S2W_Trace.thenResult]

/-- A256KiB requested-byte budget leaves at least200201 bytes after the
snapshot requests represented in this exact source interface. This is not a
whole native heap/CU budget: omitted requests/alignment remain explicit. -/
theorem snapshot_headroom (e : Entry) :
    ∃ remaining,
      reserve budget (admittedSizes e 3 firstSizes) 262144 = ok remaining ∧
      200201 ≤ remaining := by
  have bounded := first_snapshot_sum_bound e
  refine ⟨262144-(admittedSizes e 3 firstSizes).sum,?_,?_⟩
  · exact reserve_fits _ _ (by omega)
  · omega

/-- No fresh-heap assumption is hidden here: snapshot success alone cannot
justify even ONE extra child allocation at this Allocator interface. The
actual initial heap/source footprint must supply that separate inference. -/
theorem snapshot_success_not_child_admission (e : Entry) :
    reserve budget (admittedSizes e 3 firstSizes) (admittedSizes e 3 firstSizes).sum = ok 0 ∧
    reserve budget ((admittedSizes e 3 firstSizes) ++ [1])
      (admittedSizes e 3 firstSizes).sum = fail .panic := by
  constructor
  · simpa using reserve_fits (admittedSizes e 3 firstSizes) (admittedSizes e 3 firstSizes).sum (Nat.le_refl _)
  · apply reserve_insufficient
    simp

#print axioms first_snapshot_sum_bound
#print axioms reserve_fits
#print axioms reserve_insufficient
#print axioms snapshot_headroom
#print axioms snapshot_success_not_child_admission
end AspisS6SnapshotBudget
