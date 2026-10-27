import NP6_StdModel

/-! Compositional P6 result specification. Unary native/reference checks must
establish these scalar facts before this theorem can imply caller equality.
No native implementation is a parameter hidden inside this proposition. -/
set_option autoImplicit false
namespace AspisR1.NP6_ResultUniqueness

inductive Outcome (α : Type) (n : Nat) where
  | allocation : Outcome α n
  | bad : Fin n → Outcome α n
  | returned : (Fin n → α) → Outcome α n

def Characterizes {α : Type} {n : Nat} (reserved : Bool)
    (input : Fin n → Option α) (out : Outcome α n) : Prop :=
  if reserved then
    match out with
    | .allocation => False
    | .bad i => input i = none ∧ ∀ j, j.val < i.val → ∃ x, input j = some x
    | .returned values => ∀ j, input j = some (values j)
  else out = .allocation

/-- All scalar output cells and the first failing index determine the complete
Result. The shared allocator outcome remains explicit. No equality of complete
outputs occurs in the premises. -/
theorem unique {α : Type} {n : Nat} (reserved : Bool) (input : Fin n → Option α)
    (a b : Outcome α n) (ha : Characterizes reserved input a)
    (hb : Characterizes reserved input b) : a = b := by
  cases reserved with
  | false => exact ha.trans hb.symm
  | true =>
    cases a with
    | allocation => exact False.elim ha
    | bad i =>
      cases b with
      | allocation => exact False.elim hb
      | bad j =>
        have same : i = j := by
          apply Fin.ext
          rcases lt_trichotomy i.val j.val with h | h | h
          · obtain ⟨x,hx⟩ := hb.2 i h
            rw [ha.1] at hx
            cases hx
          · exact h
          · obtain ⟨x,hx⟩ := ha.2 j h
            rw [hb.1] at hx
            cases hx
        cases same
        rfl
      | returned values =>
        have impossible := hb i
        rw [ha.1] at impossible
        cases impossible
    | returned values =>
      cases b with
      | allocation => exact False.elim hb
      | bad j =>
        have impossible := ha j
        rw [hb.1] at impossible
        cases impossible
      | returned values' =>
        have same : values = values' := by
          funext j
          exact Option.some.inj ((ha j).symm.trans (hb j))
        cases same
        rfl

/-- Local inhabited result specification; not an accepted spend fixture. -/
theorem returning_nonvacuity {α : Type} {n : Nat} (x : α) :
    Characterizes true (fun _ : Fin n => some x) (.returned (fun _ => x)) := by
  intro j
  rfl

theorem allocation_nonvacuity {α : Type} {n : Nat} (input : Fin n → Option α) :
    Characterizes false input .allocation := rfl

#print axioms unique
#print axioms returning_nonvacuity
#print axioms allocation_nonvacuity
end AspisR1.NP6_ResultUniqueness
