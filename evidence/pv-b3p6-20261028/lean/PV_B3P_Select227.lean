import Aeneas.Std
namespace PV_B3P_Select227
set_option autoImplicit false

/-- The source selects the first 28 columns of each of three width-29 rows. -/
def select {α : Type} (claims : Fin 3 → Fin 29 → α) (i : Fin 84) : α :=
  claims ⟨i.val / 28, by omega⟩ ⟨i.val % 28, by omega⟩

theorem selected_column (i : Fin 84) : i.val % 28 < 28 := Nat.mod_lt _ (by omega)
theorem selected_row (i : Fin 84) : i.val / 28 < 3 := by omega

theorem row_column {α : Type} (claims : Fin 3 → Fin 29 → α)
    (row : Fin 3) (column : Fin 28) :
    select claims ⟨row.val * 28 + column.val, by omega⟩ =
      claims row ⟨column.val, by omega⟩ := by
  unfold select
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

theorem omitted_D {α : Type} (a b : Fin 3 → Fin 29 → α)
    (h : ∀ r c, c.val < 28 → a r c = b r c) : select a = select b := by
  funext i
  apply h
  exact selected_column i

/-- Ordered iteration over ranges is a fold over their concatenation. -/
theorem ordered_ranges {α β : Type} (step : α → β → α)
    (ranges : List (List β)) (initial : α) :
    ranges.foldl (fun acc range => range.foldl step acc) initial =
      ranges.flatten.foldl step initial := by
  induction ranges generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, List.flatten_cons, List.foldl_append]
    exact ih _

#print axioms selected_column
#print axioms selected_row
#print axioms row_column
#print axioms omitted_D
#print axioms ordered_ranges
end PV_B3P_Select227
