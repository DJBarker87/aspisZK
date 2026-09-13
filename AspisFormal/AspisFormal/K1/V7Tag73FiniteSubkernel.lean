import Mathlib

/-!
# Finite subkernel accounting, including decode failure and rejection

All laws are explicit nonnegative weights. No uniformity, acceptance
conditioning or source-to-model identity is implicit in these definitions.
This is a reusable arithmetic leaf, NOT the actual compiler law.
-/

set_option autoImplicit false
namespace AspisK1.V7Tag73FiniteSubkernel
open scoped BigOperators
noncomputable section
variable {A B S : Type*} [Fintype A]

/-- Unnormalised mass. Missing mass may represent abort; it is not rescaled. -/
def eventMass (w : A → ENNReal) (p : A → Prop) : ENNReal := by
  classical
  exact ∑ a, if p a then w a else 0

/-- Weighted expectation with no normalisation built in. -/
def weighted (w : A → ENNReal) (f : A → ENNReal) : ENNReal :=
  ∑ a, w a * f a

theorem eventMass_mono (w : A → ENNReal) {p q : A → Prop}
    (h : ∀ a, p a → q a) : eventMass w p ≤ eventMass w q := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : p a
  · simp [hp, h a hp]
  · simp [hp]

theorem eventMass_le_total (w : A → ENNReal) (p : A → Prop) :
    eventMass w p ≤ ∑ a, w a := by
  classical
  unfold eventMass
  exact Finset.sum_le_sum fun a _ => by split_ifs <;> simp

/-- A disjoint partition retains the entire mass, including rejection. -/
theorem eventMass_partition (w : A → ENNReal) (p q : A → Prop) :
    eventMass w p = eventMass w (fun a => p a ∧ q a) +
      eventMass w (fun a => p a ∧ ¬ q a) := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

theorem eventMass_union_le (w : A → ENNReal) (p q : A → Prop) :
    eventMass w (fun a => p a ∨ q a) ≤ eventMass w p + eventMass w q := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- Acceptance can reduce bad mass; it cannot license deleting reject mass. -/
theorem accepted_bad_mass_le (w : A → ENNReal) (accept bad : A → Prop) :
    eventMass w (fun a => accept a ∧ bad a) ≤ eventMass w bad :=
  eventMass_mono w (fun _ h => h.2)

theorem not_good_mass_le_reject_add_bad
    (w : A → ENNReal) (accept bad : A → Prop) :
    eventMass w (fun a => ¬ (accept a ∧ ¬ bad a)) ≤
      eventMass w (fun a => ¬ accept a) + eventMass w bad := by
  classical
  calc
    eventMass w (fun a => ¬ (accept a ∧ ¬ bad a)) ≤
        eventMass w (fun a => ¬ accept a ∨ bad a) := by
      apply eventMass_mono
      intro a h
      by_cases ha : accept a
      · exact Or.inr (by by_contra hb; exact h ⟨ha, hb⟩)
      · exact Or.inl ha
    _ ≤ _ := eventMass_union_le w _ _

theorem weighted_mono (w : A → ENNReal) {f g : A → ENNReal}
    (h : ∀ a, f a ≤ g a) : weighted w f ≤ weighted w g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_left' (h a) (w a)

theorem weighted_const (w : A → ENNReal) (c : ENNReal) :
    weighted w (fun _ => c) = (∑ a, w a) * c := by
  exact (Finset.sum_mul _ _ _).symm

theorem weighted_le (w : A → ENNReal) (mass_le : ∑ a, w a ≤ 1)
    (f : A → ENNReal) (c : ENNReal) (bound : ∀ a, f a ≤ c) :
    weighted w f ≤ c := by
  calc
    weighted w f ≤ weighted w (fun _ => c) := weighted_mono w bound
    _ = (∑ a, w a) * c := weighted_const w c
    _ ≤ 1 * c := mul_le_mul_right' mass_le c
    _ = c := one_mul _

/-- Composition of state-dependent raw subkernels, not an independent-product
claim about two arbitrary random variables. -/
def composedWeight [Fintype S]
    (p : S → ENNReal) (k : S → A → ENNReal) (a : A) : ENNReal :=
  ∑ s, p s * k s a

theorem composedWeight_total [Fintype S]
    (p : S → ENNReal) (k : S → A → ENNReal) :
    (∑ a, composedWeight p k a) = ∑ s, p s * ∑ a, k s a := by
  unfold composedWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact (Finset.mul_sum _ _ _).symm

theorem composedWeight_subprobability [Fintype S]
    (p : S → ENNReal) (k : S → A → ENNReal)
    (hp : ∑ s, p s ≤ 1) (hk : ∀ s, ∑ a, k s a ≤ 1) :
    (∑ a, composedWeight p k a) ≤ 1 := by
  rw [composedWeight_total]
  calc
    (∑ s, p s * ∑ a, k s a) ≤ ∑ s, p s * 1 := by
      exact Finset.sum_le_sum fun s _ => mul_le_mul_left' (hk s) (p s)
    _ = ∑ s, p s := by simp
    _ ≤ 1 := hp

/-- Decoding preserves the actual raw weights; rejected decodes have no field
value and are deliberately absent from these atom masses. -/
def decodedAtomMass (w : A → ENNReal) (decode : A → Option B) (b : B) : ENNReal :=
  eventMass w (fun a => decode a = some b)

/-- Exact fibre identity. This supports a nonuniform bounded-retry decoder:
first prove its atom masses, then bound the target, not the other way round. -/
theorem decoded_bad_mass_eq [DecidableEq B]
    (w : A → ENNReal) (decode : A → Option B) (target : Finset B) :
    eventMass w (fun a => ∃ b ∈ target, decode a = some b) =
      ∑ b ∈ target, decodedAtomMass w decode b := by
  classical
  unfold decodedAtomMass eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  cases hd : decode a with
  | none => simp [hd]
  | some b =>
      by_cases hb : b ∈ target <;> simp [hd, hb]

theorem decoded_bad_mass_le [DecidableEq B]
    (w : A → ENNReal) (decode : A → Option B) (target : Finset B)
    (atomBound : ENNReal)
    (h : ∀ b ∈ target, decodedAtomMass w decode b ≤ atomBound) :
    eventMass w (fun a => ∃ b ∈ target, decode a = some b) ≤
      (target.card : ENNReal) * atomBound := by
  rw [decoded_bad_mass_eq]
  calc
    (∑ b ∈ target, decodedAtomMass w decode b) ≤ ∑ _b ∈ target, atomBound := by
      exact Finset.sum_le_sum fun b hb => h b hb
    _ = (target.card : ENNReal) * atomBound := by simp [nsmul_eq_mul]

/-- Split decode failure from successfully decoded bad values. -/
theorem decode_failure_or_bad_le [DecidableEq B]
    (w : A → ENNReal) (decode : A → Option B) (target : Finset B)
    (atomBound : ENNReal)
    (h : ∀ b ∈ target, decodedAtomMass w decode b ≤ atomBound) :
    eventMass w (fun a => decode a = none ∨ ∃ b ∈ target, decode a = some b) ≤
      eventMass w (fun a => decode a = none) + (target.card : ENNReal) * atomBound := by
  exact (eventMass_union_le w _ _).trans
    (add_le_add le_rfl (decoded_bad_mass_le w decode target atomBound h))

#print axioms eventMass_partition
#print axioms not_good_mass_le_reject_add_bad
#print axioms composedWeight_subprobability
#print axioms decoded_bad_mass_eq
#print axioms decoded_bad_mass_le
#print axioms decode_failure_or_bad_le
end
end AspisK1.V7Tag73FiniteSubkernel
