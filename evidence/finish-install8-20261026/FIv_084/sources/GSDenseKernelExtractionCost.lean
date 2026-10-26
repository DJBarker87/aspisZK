import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import GSDenseRrefLoopFullWorkCost

set_option autoImplicit false

namespace CompPoly.DenseMatrix

variable {F : Type*}

/-- A short-circuit scan of a natural-number list, paired with the number of
equality tests actually performed before the first match (or end of list). -/
def containsNatListCounted : List Nat → Nat → Bool × Nat
  | [], _ => (false, 0)
  | x :: xs, key =>
      if x == key then (true, 1)
      else
        let rest := containsNatListCounted xs key
        (rest.1, rest.2 + 1)

theorem containsNatListCounted_refines (xs : List Nat) (key : Nat) :
    (containsNatListCounted xs key).1 = xs.any (fun x => x == key) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : (x == key) <;> simp [containsNatListCounted, h, ih]

theorem containsNatListCounted_cost_le (xs : List Nat) (key : Nat) :
    (containsNatListCounted xs key).2 ≤ xs.length := by
  induction xs with
  | nil => simp [containsNatListCounted]
  | cons x xs ih =>
      cases h : (x == key) <;>
        simp [containsNatListCounted, h] at * <;>
        omega

/-- The production free-column filter, instrumented with one unit for each
candidate column and one for each membership equality test performed. -/
def freeColumnsListCounted (pivots : Array Nat) :
    List Nat → List Nat × Nat
  | [] => ([], 0)
  | col :: cols =>
      let hit := containsNatListCounted pivots.toList col
      let rest := freeColumnsListCounted pivots cols
      (if hit.1 then rest.1 else col :: rest.1, 1 + hit.2 + rest.2)

theorem freeColumnsListCounted_refines (pivots : Array Nat) (cols : List Nat) :
    (freeColumnsListCounted pivots cols).1 =
      cols.filter (fun col => !(containsNat pivots col)) := by
  induction cols with
  | nil => rfl
  | cons col cols ih =>
      have hcontains : containsNat pivots col =
          (containsNatListCounted pivots.toList col).1 := by
        simp [containsNat, containsNatListCounted_refines]
      cases h : containsNat pivots col <;>
        simp only [freeColumnsListCounted, Prod.fst]
      all_goals rw [← hcontains]
      all_goals simp [h, ih]

theorem freeColumnsListCounted_cost_le (pivots : Array Nat) (cols : List Nat) :
    (freeColumnsListCounted pivots cols).2 ≤ cols.length * (pivots.size + 1) := by
  induction cols with
  | nil => simp [freeColumnsListCounted]
  | cons col cols ih =>
      have hscan := containsNatListCounted_cost_le pivots.toList col
      simp only [freeColumnsListCounted, Prod.snd]
      have hpivots : pivots.toList.length = pivots.size := by simp
      rw [hpivots] at hscan
      rw [List.length_cons]
      rw [Nat.succ_mul]
      omega

def freeColumnsCounted (cols : Nat) (pivots : Array Nat) :
    Array Nat × Nat :=
  let result := freeColumnsListCounted pivots (List.range cols)
  (result.1.toArray, result.2)

theorem freeColumnsCounted_refines (cols : Nat) (pivots : Array Nat) :
    (freeColumnsCounted cols pivots).1 = freeColumns cols pivots := by
  simp [freeColumnsCounted, freeColumns, freeColumnsListCounted_refines]

theorem freeColumnsCounted_cost_le (cols : Nat) (pivots : Array Nat) :
    (freeColumnsCounted cols pivots).2 ≤ cols * (pivots.size + 1) := by
  have h := freeColumnsListCounted_cost_le pivots (List.range cols)
  change (freeColumnsListCounted pivots (List.range cols)).2 ≤
    cols * (pivots.size + 1)
  simpa using h

/-- A short-circuit `find?` scan paired with its number of predicate tests. -/
def findCounted {α : Type*} (p : α → Bool) : List α → Option α × Nat
  | [] => (none, 0)
  | x :: xs =>
      if p x then (some x, 1)
      else
        let rest := findCounted p xs
        (rest.1, rest.2 + 1)

theorem findCounted_refines {α : Type*} (p : α → Bool) (xs : List α) :
    (findCounted p xs).1 = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;> simp [findCounted, h, ih]

theorem findCounted_cost_le {α : Type*} (p : α → Bool) (xs : List α) :
    (findCounted p xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [findCounted]
  | cons x xs ih =>
      cases h : p x <;>
        simp [findCounted, h] at * <;>
        omega

def pivotRowOfColumnCounted (pivots : Array Nat) (col : Nat) :
    Option Nat × Nat :=
  findCounted (fun row => pivots.getD row 0 == col) (List.range pivots.size)

theorem pivotRowOfColumnCounted_refines (pivots : Array Nat) (col : Nat) :
    (pivotRowOfColumnCounted pivots col).1 = pivotRowOfColumn? pivots col := by
  unfold pivotRowOfColumnCounted pivotRowOfColumn?
  exact findCounted_refines (fun row => pivots.getD row 0 == col)
    (List.range pivots.size)

theorem pivotRowOfColumnCounted_cost_le (pivots : Array Nat) (col : Nat) :
    (pivotRowOfColumnCounted pivots col).2 ≤ pivots.size := by
  have h := findCounted_cost_le (fun row => pivots.getD row 0 == col)
    (List.range pivots.size)
  simpa [pivotRowOfColumnCounted] using h

/-- The ordinary coordinate-vector output is retained; the accompanying count
charges one coordinate construction per output cell and the exact pivot-row
search length for each non-free coordinate. -/
def basisVectorForFreeColumnCounted [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (free : Nat) : Array F × Nat :=
  let cost := (List.finRange A.cols).foldl
    (fun total i =>
      total + 1 + if i.val == free then 0
        else (pivotRowOfColumnCounted pivots i.val).2)
    0
  (basisVectorForFreeColumn A pivots free, cost)

theorem basisVectorForFreeColumnCounted_refines [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (free : Nat) :
    (basisVectorForFreeColumnCounted A pivots free).1 =
      basisVectorForFreeColumn A pivots free := rfl

private theorem finRange_fold_cost_le (pivots : Array Nat) (free cols : Nat) :
    ((List.finRange cols).foldl
      (fun total i => total + 1 + if i.val == free then 0
        else (pivotRowOfColumnCounted pivots i.val).2) 0) ≤
      cols * (pivots.size + 1) := by
  have hgen : ∀ (xs : List (Fin cols)) (total : Nat),
      xs.foldl (fun total i => total + 1 + if i.val == free then 0
        else (pivotRowOfColumnCounted pivots i.val).2) total ≤
        total + xs.length * (pivots.size + 1) := by
    intro xs
    induction xs with
    | nil => intro total; simp
    | cons i xs ih =>
        intro total
        simp only [List.foldl_cons, List.length_cons]
        have hscan := pivotRowOfColumnCounted_cost_le pivots i.val
        have hone : 1 + (if i.val == free then 0
            else (pivotRowOfColumnCounted pivots i.val).2) ≤ pivots.size + 1 := by
          cases heq : (i.val == free) <;> simp [heq] <;> omega
        have htail := ih (total + 1 + if i.val == free then 0
          else (pivotRowOfColumnCounted pivots i.val).2)
        rw [Nat.succ_mul]
        omega
  have h := hgen (List.finRange cols) 0
  simpa using h

theorem basisVectorForFreeColumnCounted_cost_le [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (free : Nat) :
    (basisVectorForFreeColumnCounted A pivots free).2 ≤
      A.cols * (pivots.size + 1) := by
  simpa [basisVectorForFreeColumnCounted] using
    finRange_fold_cost_le pivots free A.cols

#print axioms freeColumnsCounted_refines
#print axioms freeColumnsCounted_cost_le
#print axioms pivotRowOfColumnCounted_refines
#print axioms pivotRowOfColumnCounted_cost_le
#print axioms basisVectorForFreeColumnCounted_refines
#print axioms basisVectorForFreeColumnCounted_cost_le

end CompPoly.DenseMatrix
