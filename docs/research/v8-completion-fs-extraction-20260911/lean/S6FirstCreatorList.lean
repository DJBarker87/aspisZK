import Std

/-! FIRST-ATTEMPT draft. This only locates an earliest key in a complete
chronological list. Source cache consistency must identify the earliest
entry as a genuine fresh exposure and preserve its answer. -/
set_option autoImplicit false
namespace AspisS6.FirstCreator
universe u v
variable {I : Type u} {O : Type v} [DecidableEq I]

def first (key : I) : List (I × O) → Option O
  | [] => none
  | (input, output) :: rest => if input = key then some output else first key rest

theorem first_append_when_absent (key : I) (left right : List (I × O))
    (absent : first key left = none) : first key (left ++ right) = first key right := by
  induction left with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨input, output⟩
      by_cases same : input = key
      · simp [first, same] at absent
      · simp only [first, if_neg same] at absent
        simpa only [List.cons_append, first, if_neg same] using ih absent

/-- Appending a cache replay cannot replace an already present creator. -/
theorem first_append_when_present (key : I) (left right : List (I × O))
    (value : O) (present : first key left = some value) :
    first key (left ++ right) = some value := by
  induction left with
  | nil => simp [first] at present
  | cons pair rest ih =>
      rcases pair with ⟨input, output⟩
      by_cases same : input = key
      · simpa only [List.cons_append, first, if_pos same] using present
      · simp only [first, if_neg same] at present
        simpa only [List.cons_append, first, if_neg same] using ih present

#print axioms first_append_when_absent
#print axioms first_append_when_present
end AspisS6.FirstCreator

