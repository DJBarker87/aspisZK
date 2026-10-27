import R1Z.PV_CBM_InventoryShape
namespace R1Z.PV_CBM_CellEnumeration
set_option autoImplicit false

def rectangle (rows columns : List Nat) : List (Nat × Nat) :=
  columns.flatMap (fun column => rows.map (fun row => (row,column)))

theorem rectangle_nil (rows : List Nat) : rectangle rows [] = [] := rfl

theorem rectangle_cons (rows : List Nat) (column : Nat) (columns : List Nat) :
    rectangle rows (column :: columns) =
      rows.map (fun row => (row,column)) ++ rectangle rows columns := rfl

theorem rectangle_length (rows columns : List Nat) :
    (rectangle rows columns).length = rows.length * columns.length := by
  induction columns with
  | nil => simp only [rectangle_nil, List.length_nil, Nat.mul_zero]
  | cons column columns ih =>
    rw [rectangle_cons, List.length_append, List.length_map, ih, List.length_cons,
      Nat.mul_succ]
    omega

theorem rectangle_append (rows left right : List Nat) :
    rectangle rows (left ++ right) = rectangle rows left ++ rectangle rows right := by
  induction left with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, rectangle_cons, ih, List.append_assoc]

#print axioms rectangle_nil
#print axioms rectangle_cons
#print axioms rectangle_length
#print axioms rectangle_append
end R1Z.PV_CBM_CellEnumeration
