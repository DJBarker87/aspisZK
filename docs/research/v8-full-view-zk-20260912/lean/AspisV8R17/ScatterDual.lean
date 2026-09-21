import AspisV8R17.WeightedScatter
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Adjoint of the retained source scatter schedule, with explicit bounds.
The gather is the weighted reads of opening_weights::xt, not a dense matrix
assumed equal to it. Rust word/field refinement remains separate. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def gatherValue (edges : List (ScatterEdge ℕ ℕ F)) (w : ℕ → F) (i : ℕ) : F :=
  (edges.map fun e => if i=e.1 then e.2.2*w e.2.1 else 0).sum

theorem scatter_gather_dot (edges : List (ScatterEdge ℕ ℕ F)) (n m : ℕ)
    (bounds : ∀ e ∈ edges, e.1<n ∧ e.2.1<m) (q w : ℕ → F) :
    (∑ r ∈ Finset.range m, w r * scatterValue edges q r) =
      ∑ i ∈ Finset.range n, gatherValue edges w i * q i := by
  induction edges with
  | nil => simp [scatterValue, gatherValue]
  | cons e es ih =>
    obtain ⟨hi,hj⟩ := bounds e (by simp)
    have tail := ih (fun e he => bounds e (by simp [he]))
    simp only [scatterValue, gatherValue, List.map_cons, List.sum_cons] at tail ⊢
    simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul,
      mul_zero, zero_mul]
    rw [tail]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hi, hj, if_true]
    ring

theorem gather_append (xs ys : List (ScatterEdge ℕ ℕ F)) (w : ℕ → F) (i : ℕ) :
    gatherValue (xs++ys) w i = gatherValue xs w i + gatherValue ys w i := by
  simp [gatherValue, List.map_append, List.sum_append]

theorem gather_column (edges : List (ℕ × F)) (j i : ℕ) (w : ℕ → F) :
    gatherValue (edges.map fun e => (j,e.1,e.2)) w i =
      if i=j then (edges.map fun e => e.2*w e.1).sum else 0 := by
  by_cases h : i=j <;> simp [gatherValue, List.map_map, Function.comp_def, h]

theorem gather_columns (columns : List ℕ) (edges : ℕ → List (ℕ × F))
    (w : ℕ → F) (i : ℕ) :
    gatherValue (columns.flatMap fun j => (edges j).map fun e => (j,e.1,e.2)) w i =
      (columns.map fun j => if j=i then ((edges j).map fun e => e.2*w e.1).sum else 0).sum := by
  induction columns with
  | nil => simp [gatherValue]
  | cons j js ih =>
    simp only [List.flatMap_cons, gather_append, gather_column, ih,
      List.map_cons, List.sum_cons]
    by_cases h : i=j <;> simp [h, Ne.symm]

def sourceGather (half : F) (w : ℕ → F) (i : ℕ) : F :=
  (((weightedIndexLoop half 10 i 0 1).getD []).map fun e => e.2*w e.1).sum

theorem source_gather_eq (half : F) (n i : ℕ) (hi : i<n) (w : ℕ → F) :
    gatherValue (sourceEdges half n) w i = sourceGather half w i := by
  rw [sourceEdges, gather_columns, range_unit_sum, if_pos hi]
  rfl

theorem source_scatter_gather_dot (half : F) (n : ℕ)
    (bounded : scheduleBounded n = true) (q w : ℕ → F) :
    (∑ r ∈ Finset.range (n+1), w r * scatterValue (sourceEdges half n) q r) =
      ∑ i ∈ Finset.range n, sourceGather half w i * q i := by
  rw [scatter_gather_dot _ n (n+1)
    (fun e he => sourceEdges_bounds half n bounded e he)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [source_gather_eq half n i (Finset.mem_range.mp hi)]

#print axioms scatter_gather_dot
#print axioms source_gather_eq
#print axioms source_scatter_gather_dot
end AspisV8R17
