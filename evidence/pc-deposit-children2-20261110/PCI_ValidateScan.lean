import Aeneas
set_option autoImplicit false
namespace PCI_ValidateScan
/-- Source-ordered short-circuit fold for the exact native any predicate. -/
def run {T : Type} (pred : T → Bool) : List T → Bool
  | [] => false
  | x::xs => if pred x then true else run pred xs

theorem step {T : Type} (pred : T → Bool) (x : T) (xs : List T) :
    run pred (x::xs) = if pred x then true else run pred xs := rfl

theorem complete {T : Type} (pred : T → Bool) (xs : List T) :
    run pred xs = xs.any pred := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [run,List.any_cons]
    rw [ih]
    cases pred x <;> rfl

/-- An accepting prefix never evaluates an invented suffix; no account or
    runtime event is introduced by the pure predicate fold. -/
def visited {T : Type} (pred : T → Bool) : List T → List T
  | [] => []
  | x::xs => if pred x then [x] else x::visited pred xs

theorem visited_prefix {T : Type} (pred : T → Bool) (xs : List T) :
    ∃ suffix, visited pred xs ++ suffix = xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    by_cases h : pred x = true
    · exact ⟨xs,by simp [visited,h]⟩
    · obtain ⟨suffix,hs⟩ := ih
      exact ⟨suffix,by simpa [visited,h] using congrArg (List.cons x) hs⟩

#print axioms step
#print axioms complete
#print axioms visited_prefix
end PCI_ValidateScan
