import SelectorExpansionOuter
import SelectedSelectorExpansionCore

/-! Adapter from the mechanically proved Aeneas expansion loop to the old
pure `SelectedSelectorExpansion` recurrence. The product theorem itself is
reused from that module. -/
set_option autoImplicit false
namespace AspisR1.SelectorExpansionOldAdapter

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorExpansionCorrectness
open AspisR1.SelectorExpansionOuter
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

/-- The generated two-store update is the same total-function update as the
old pure source-store model. -/
theorem selectorWrite_eq_sourceStores (x : ExactQM) (i : Nat)
    (w : Nat → ExactQM) :
    selectorWrite x i w = AspisV8.SelectedSelectorExpansion.sourceStores w x i := by
  rfl

/-- The actual-loop recurrence is definitionally the old descending source
pass after the two-store adapter. -/
theorem selectorWrite_eq_writePair (x : ExactQM) (i : Nat)
    (w : Nat → ExactQM) :
    selectorWrite x i w = AspisV8.SelectedSelectorExpansion.writePair w x i := by
  calc
    selectorWrite x i w = AspisV8.SelectedSelectorExpansion.sourceStores w x i :=
      selectorWrite_eq_sourceStores x i w
    _ = AspisV8.SelectedSelectorExpansion.writePair w x i :=
      AspisV8.SelectedSelectorExpansion.sourceStores_eq w x i

theorem selectorDescending_eq (x : ExactQM) (n : Nat) (w : Nat → ExactQM) :
    selectorDescending x n w = AspisV8.SelectedSelectorExpansion.descendingPass x n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      change selectorDescending x n (selectorWrite x n w) =
        AspisV8.SelectedSelectorExpansion.descendingPass x n
          (AspisV8.SelectedSelectorExpansion.writePair w x n)
      rw [ih, selectorWrite_eq_writePair]

/-- Reuse the prior exact pointwise expansion theorem for every array cell. -/
theorem selectorDescending_lookup (x : ExactQM) (n : Nat) (w : Nat → ExactQM)
    (j : Nat) (hj : j < 2*n) :
    selectorDescending x n w j =
      w (j/2) * selectorFactor x (j.testBit 0) := by
  rw [selectorDescending_eq]
  simpa [selectorFactor, AspisV8.SelectedSelectorExpansion.factor] using
    (AspisV8.SelectedSelectorExpansion.descendingPass_lookup x n w j hj)

/-- Exact decoded coordinate list, with zero outside its finite range. -/
def exactCoordinates (xs : List QM) (i : Nat) : ExactQM :=
  if h : i < xs.length then decode (xs[i]'h) else 0

/-- Exact-field version of the list fold used by the generated-array proof. -/
def expandExactListModel : List ExactQM → Nat → (Nat → ExactQM) → Nat → ExactQM
  | [], _, w, j => w j
  | x :: xs, level, w, j =>
      expandExactListModel xs (level + 1)
        (AspisV8.SelectedSelectorExpansion.descendingPass x (2 ^ level) w) j

private theorem expandListModel_to_exact (xs : List QM) (level : Nat)
    (w : Nat → ExactQM) (j : Nat) :
    expandListModel xs level w j =
      expandExactListModel (xs.map decode) level w j := by
  induction xs generalizing level w with
  | nil => rfl
  | cons x xs ih =>
      simp only [expandListModel, List.map_cons]
      rw [selectorDescending_eq]
      exact ih (level + 1) _

/-- General alignment lemma: a finite coordinate list starting at `level`
implements the old recursively-defined expansion up to its final length. -/
theorem expandExactListModel_eq_expand
    (xs : List ExactQM) (level : Nat) (z : Nat → ExactQM)
    (w : Nat → ExactQM) (j : Nat)
    (hinit : ∀ k, w k = AspisV8.SelectedSelectorExpansion.expand z level k)
    (hcoords : ∀ (i : Nat) (hi : i < xs.length),
      xs[i]'hi = z (level+i)) :
    expandExactListModel xs level w j =
      AspisV8.SelectedSelectorExpansion.expand z (level + xs.length) j := by
  induction xs generalizing level w with
  | nil =>
      exact hinit j
  | cons x xs ih =>
      have hzero : 0 < (x :: xs).length := by simp
      have hx : x = z level := by simpa using hcoords 0 hzero
      have hnext :
          AspisV8.SelectedSelectorExpansion.descendingPass x (2 ^ level) w =
          AspisV8.SelectedSelectorExpansion.expand z (level+1) := by
        have hw : w = AspisV8.SelectedSelectorExpansion.expand z level := funext hinit
        rw [hw, hx]
        simp only [AspisV8.SelectedSelectorExpansion.expand]
        rw [← AspisV8.SelectedSelectorExpansion.sourcePass_eq]
      have htailCoords : ∀ (i : Nat) (hi : i < xs.length),
          xs[i]'hi = z (level+1+i) := by
        intro i hi
        have hsucc : i+1 < (x :: xs).length := by simp; omega
        have h := hcoords (i+1) hsucc
        have hlevel : level + (i+1) = level + 1 + i := by omega
        simp only [List.getElem_cons_succ] at h
        rw [hlevel] at h
        exact h
      simp only [expandExactListModel]
      rw [hnext]
      have hend : level + 1 + xs.length = level + (x :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [← hend]
      exact ih (level+1) (AspisV8.SelectedSelectorExpansion.expand z (level+1))
        (by intro k; rfl) htailCoords

/-- The old recursively-defined expansion for the decoded list uses the
same one-hot initial state as the generated wrapper. -/
theorem expandListModel_eq_expand
    (xs : List QM) (j : Nat) :
    expandListModel xs 0 (fun i => if i = 0 then 1 else 0) j =
      AspisV8.SelectedSelectorExpansion.expand
        (exactCoordinates xs) xs.length j := by
  rw [expandListModel_to_exact]
  simpa only [List.length_map, Nat.zero_add] using
    (expandExactListModel_eq_expand (xs.map decode) 0 (exactCoordinates xs)
      (fun i => if i = 0 then 1 else 0) j
      (by intro k; simp [AspisV8.SelectedSelectorExpansion.expand])
      (by
        intro i hi
        have hi' : i < xs.length := by simpa using hi
        simp [exactCoordinates, hi']))

/-- The old product theorem is the endpoint; no product proof is repeated. -/
theorem generated_expand_product
    (xs : List QM) (j : Nat) (hj : j < 2 ^ xs.length) :
    expandListModel xs 0 (fun i => if i = 0 then 1 else 0) j =
      AspisV8.SelectedSelectorExpansion.tensorProduct (exactCoordinates xs) xs.length j := by
  rw [expandListModel_eq_expand]
  exact AspisV8.SelectedSelectorExpansion.expand_product
    (exactCoordinates xs) xs.length j hj

/-- The generated mutable-array loop exposes the reused pure product at every
in-range row, with canonicality inherited from the actual prepared arithmetic. -/
theorem expand_model_product
    (N : Usize) (coordinates : Slice QM)
    (hcapacity : 2 ^ coordinates.val.length ≤ N.val)
    (hcoords : ∀ x ∈ coordinates.val, Canonical x)
    (j : Nat) (hj : j < 2 ^ coordinates.val.length) :
    ∃ out : Array QM N,
      pool_v1.pair_forest_copy_terminal.Selectors.expand N coordinates = .ok out ∧
      canonicalArray out ∧
      decodedArray out j =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactCoordinates coordinates.val) coordinates.val.length j := by
  obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
    expand_model N coordinates hcapacity hcoords
  have hjN : j < N.val := lt_of_lt_of_le hj hcapacity
  refine ⟨out, hrun, hcanonical, ?_⟩
  calc
    decodedArray out j =
        expandListModel coordinates.val 0 (fun i => if i = 0 then 1 else 0) j :=
      hmodel ⟨j, hjN⟩
    _ = AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactCoordinates coordinates.val) coordinates.val.length j :=
      generated_expand_product coordinates.val j hj

#print axioms selectorWrite_eq_sourceStores
#print axioms selectorDescending_eq
#print axioms selectorDescending_lookup
#print axioms expandExactListModel_eq_expand
#print axioms expandListModel_eq_expand
#print axioms generated_expand_product
#print axioms expand_model_product
end AspisR1.SelectorExpansionOldAdapter
