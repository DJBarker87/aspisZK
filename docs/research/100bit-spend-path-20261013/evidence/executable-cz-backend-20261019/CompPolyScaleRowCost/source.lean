import CompPoly.LinearAlgebra.Dense.KernelInPlace

namespace CompPoly.DenseMatrix

universe u v

private theorem foldl_pair_cost_length {α : Type u} {β : Type v}
    (f : α × Nat → β → α × Nat)
    (hf : ∀ p x, (f p x).2 = p.2 + 1) :
    ∀ (p : α × Nat) (xs : List β),
      (xs.foldl f p).2 = p.2 + xs.length := by
  intro p xs
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (p := f p x), hf, List.length_cons]
      omega

private theorem foldl_pair_first {α : Type u} {β : Type v}
    (f : α × Nat → β → α × Nat)
    (g : α → β → α) (hf : ∀ p x, (f p x).1 = g p.1 x) :
    ∀ (p : α × Nat) (xs : List β),
      (xs.foldl f p).1 = xs.foldl g p.1 := by
  intro p xs
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih (p := f p x), hf, List.foldl_cons]

/-- Instrumented form of the actual in-place row scaling loop.  The counter is
incremented exactly beside its one field multiplication. -/
def scaleRowDataCounted [Field F] (cols row : Nat) (factor : F)
    (data : Array F) : Array F × Nat :=
  (List.range' 0 cols).foldl (fun p col =>
    (setD p.1 (row * cols + col) (factor * p.1.getD (row * cols + col) 0), p.2 + 1))
    (data, 0)

/-- The instrumented loop performs exactly one field multiplication per column. -/
theorem scaleRowDataCounted_cost [Field F] (cols row : Nat) (factor : F)
    (data : Array F) : (scaleRowDataCounted cols row factor data).2 = cols := by
  unfold scaleRowDataCounted
  let f : Array F × Nat → Nat → Array F × Nat := fun p col =>
    (setD p.1 (row * cols + col) (factor * p.1.getD (row * cols + col) 0), p.2 + 1)
  change (((List.range' 0 cols).foldl f (data, 0)).2) = cols
  have h := foldl_pair_cost_length (α := Array F) (β := Nat) f
    (by intro p col; rfl) (data, 0) (List.range' 0 cols)
  simpa using h

/-- Instrumentation preserves the exact array produced by CompPoly's in-place
scaleRowData implementation. -/
theorem scaleRowDataCounted_refines [Field F] (cols row : Nat) (factor : F)
    (data : Array F) : (scaleRowDataCounted cols row factor data).1 =
      scaleRowData cols row factor data := by
  unfold scaleRowDataCounted
  let f : Array F × Nat → Nat → Array F × Nat := fun p col =>
    (setD p.1 (row * cols + col) (factor * p.1.getD (row * cols + col) 0), p.2 + 1)
  let g : Array F → Nat → Array F := fun d col =>
    setD d (row * cols + col) (factor * d.getD (row * cols + col) 0)
  have hfirst := foldl_pair_first (f := f) (g := g) (by
    intro p col
    rfl) (data, 0) (List.range' 0 cols)
  calc
    _ = (List.range' 0 cols).foldl g data := hfirst
    _ = scaleRowData cols row factor data := by
      simp [scaleRowData, g, Std.Legacy.Range.forIn_eq_forIn_range']

end CompPoly.DenseMatrix

#print axioms CompPoly.DenseMatrix.scaleRowDataCounted_cost
#print axioms CompPoly.DenseMatrix.scaleRowDataCounted_refines
