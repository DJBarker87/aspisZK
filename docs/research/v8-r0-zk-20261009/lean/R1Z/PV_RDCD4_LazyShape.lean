import R1Z.PV_RDCD4_LazyCell
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyShape
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell

def shape {T : Type} (rows : List (List T)) : Prop :=
  rows.length=3 ∧ ∀ row ∈ rows, row.length=3

/-- Concrete initialized constructor witness for every nine scalar values. -/
theorem literal_shape {T : Type} (a b c d e f g h i : T) :
    shape [[a,b,c],[d,e,f],[g,h,i]] := by
  simp [shape]

theorem row_bound {T : Type} (rows : List (List T)) (h : shape rows)
    (i : Nat) (hi : i < 3) : i < rows.length := by rw [h.1];exact hi

theorem col_bound {T : Type} (rows : List (List T)) (h : shape rows)
    (i j : Nat) (hi : i < 3) (hj : j < 3) :
    j < (rows[i]'(row_bound rows h i hi)).length := by
  rw [h.2 _ (List.getElem_mem (row_bound rows h i hi))]
  exact hj

theorem read_guards {T : Type} (rows : List (List T)) (h : shape rows)
    (i j : Nat) (hi : i < 3) (hj : j < 3) :
    ∃ row, read rows i=ok row ∧ ∃ value, read row j=ok value := by
  refine ⟨rows[i]'(row_bound rows h i hi),PV_RDCD3_Index194.success rows i (row_bound rows h i hi),?_⟩
  exact ⟨(rows[i]'(row_bound rows h i hi))[j]'(col_bound rows h i j hi hj),
    PV_RDCD3_Index194.success _ j (col_bound rows h i j hi hj)⟩

theorem all_set {T : Type} (p : T → Prop) (xs : List T) (i : Nat) (v : T)
    (hx : ∀ x ∈ xs,p x) (hv : p v) : ∀ x ∈ xs.set i v,p x := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simpa using And.intro hv (fun y hy => hx y (by simp [hy]))
    | succ i =>
      simp only [List.set_cons_succ,List.mem_cons]
      intro y hy
      cases hy with
      | inl he => subst y;exact hx x (by simp)
      | inr hm => exact ih i (fun z hz => hx z (by simp [hz])) y hm

theorem update_shape {T : Type} (rows : List (List T)) (h : shape rows)
    (i j : Nat) (v : T) (hi : i < 3) :
    shape (rows.set i ((rows[i]'(row_bound rows h i hi)).set j v)) := by
  constructor
  · simpa only [List.length_set] using h.1
  · apply all_set (fun row : List T => row.length=3) rows i _ h.2
    simpa only [List.length_set] using h.2 _ (List.getElem_mem (row_bound rows h i hi))

#print axioms literal_shape
#print axioms read_guards
#print axioms row_bound
#print axioms col_bound
#print axioms update_shape
end R1Z.PV_RDCD4_LazyShape
