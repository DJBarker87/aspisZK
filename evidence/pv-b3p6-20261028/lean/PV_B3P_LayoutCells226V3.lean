import PV_B3P_ByteLayout226V3
namespace PV_B3P_LayoutCells226V3
open Aeneas Aeneas.Std PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem flat_cell {A B : Type} (n : Nat) (f : A → List B)
    (arity : ∀ x, (f x).length = n) (xs : List A) (i j : Nat)
    (hi : i < xs.length) (hj : j < n) :
    (xs.flatMap f)[n*i+j]? = (f xs[i])[j]? := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons x tail =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add]
      rw [List.getElem?_append_left (by rw [arity]; exact hj)]
      rfl
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons x tail =>
      rw [List.flatMap_cons,List.getElem?_append_right
        (by rw [arity]; simp only [Nat.mul_succ]; omega),arity]
      have offset : n*(i+1)+j-n = n*i+j := by rw [Nat.mul_succ]; omega
      rw [offset,ih tail (by simpa using hi)]
      rfl

theorem fields_cell (xs : List U32) (i j : Nat) (hi : i < xs.length) (hj : j < 4) :
    (fields xs)[4*i+j]? = (wordBytes xs[i])[j]? :=
  flat_cell 4 wordBytes (fun _ => rfl) xs i j hi hj

theorem frontier_cell (a : Array (Array U32 8#usize) 20#usize)
    (i j : Nat) (hi : i < a.val.length) (hj : j < 8) :
    (frontier a)[8*i+j]? = a.val[i].val[j]? := by
  apply flat_cell 8 (fun row : Array U32 8#usize => row.val) _ a.val i j hi hj
  intro row
  exact row.property

#print axioms flat_cell
#print axioms fields_cell
#print axioms frontier_cell
end PV_B3P_LayoutCells226V3
