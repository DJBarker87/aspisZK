import Port5Q1_GeometryModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_ListCells
open Aeneas Aeneas.Std
abbrev FP := ZMod AspisCircleGroupOrder.P

theorem map_cell (xs : List U32) (i : Nat) :
    (xs.map S7JoinBasisMachine.decode)[i]?.getD 0=
      S7JoinBasisMachine.decode (xs[i]?.getD 0#u32) := by
  rw [List.getElem?_map]
  cases xs[i]? <;> rfl

theorem flat_cell {A B : Type} (f : A → List B) (arity : ∀ x, (f x).length=5)
    (xs : List A) (i j : Nat) (hi : i<xs.length) (hj : j<5) :
    (xs.flatMap f)[5*i+j]?=(f xs[i])[j]? := by
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
      rw [List.flatMap_cons,List.getElem?_append_right (by rw [arity]; omega),arity]
      have offset : 5*(i+1)+j-5=5*i+j := by omega
      rw [offset,ih tail (by simpa using hi)]
      rfl

theorem record_cell (flat : alloc.vec.Vec U32) (i : Nat) (j : Fin 5) :
    (Port4C_CollectLoop.record flat i).val[j.val]?.getD 0#u32=
      Port4C_BatchInverse.cell flat.val (5*i+j.val) := by
  fin_cases j <;> rfl

#print axioms map_cell
#print axioms flat_cell
#print axioms record_cell
end AspisR1.Port5Q1_ListCells
end
