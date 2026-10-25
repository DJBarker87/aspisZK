import NP6_ResultUniqueness
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ScalarResult
open NP6_ResultUniqueness
attribute [local instance] Classical.propDecidable

def Canonical {limbs : Nat} (threshold : Nat) (row : Fin limbs → Nat) : Prop :=
  ∀ l, row l < threshold

/-- Exactly the unary gate interface: all output limbs, a bad-limb witness,
and canonical prior fields. Allocation availability remains the shared item. -/
def Characterizes {n limbs : Nat} (reserved : Bool) (threshold : Nat)
    (input : Fin n → Fin limbs → Nat) (out : Outcome (Fin limbs → Nat) n) : Prop :=
  if reserved then
    match out with
    | .allocation => False
    | .bad bad => (∃ l, threshold ≤ input bad l) ∧
        ∀ before, before.val < bad.val → Canonical threshold (input before)
    | .returned values => ∀ i l, input i l < threshold ∧ values i l = input i l
  else out = .allocation

theorem to_option_spec {n limbs : Nat} (reserved : Bool) (threshold : Nat)
    (input : Fin n → Fin limbs → Nat) (out : Outcome (Fin limbs → Nat) n)
    (facts : Characterizes reserved threshold input out) :
    NP6_ResultUniqueness.Characterizes reserved
      (fun i => if Canonical threshold (input i) then some (input i) else none) out := by
  classical
  cases reserved with
  | false => exact facts
  | true =>
    cases out with
    | allocation => exact False.elim facts
    | bad bad =>
      have invalid : ¬ Canonical threshold (input bad) := by
        intro good
        obtain ⟨l,large⟩ := facts.1
        exact (Nat.not_lt_of_ge large) (good l)
      refine ⟨by simp [invalid],?_⟩
      intro before earlier
      exact ⟨input before,by simp [facts.2 before earlier]⟩
    | returned values =>
      intro i
      have good : Canonical threshold (input i) := fun l => (facts i l).1
      have same : values i = input i := by
        funext l
        exact (facts i l).2
      simp [good,same]

/-- Kernel-checked composition of the two concrete unary P6 gate interfaces.
No equality of caller outputs is a premise; no concrete gate is assumed here. -/
theorem unique {n limbs : Nat} (reserved : Bool) (threshold : Nat)
    (input : Fin n → Fin limbs → Nat) (native reference : Outcome (Fin limbs → Nat) n)
    (hn : Characterizes reserved threshold input native)
    (hr : Characterizes reserved threshold input reference) : native = reference := by
  classical
  exact NP6_ResultUniqueness.unique reserved _ native reference
    (to_option_spec reserved threshold input native hn)
    (to_option_spec reserved threshold input reference hr)

#print axioms to_option_spec
#print axioms unique
end AspisR1.NP6_ScalarResult
end
