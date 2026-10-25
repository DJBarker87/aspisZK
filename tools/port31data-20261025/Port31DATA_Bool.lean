import Init

/-- Fresh compatibility proof selection, not the recovered historical Bool helper. -/
theorem Port31DATA.eq_true_of_not_eq_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b with
  | false => exact False.elim (h rfl)
  | true => rfl

set_option pp.all true in
#print Port31DATA.eq_true_of_not_eq_false
#print axioms Port31DATA.eq_true_of_not_eq_false
