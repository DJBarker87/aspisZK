import M31RejectFiber
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev RetryWords := Fin 16 → Word
abbrev OutputNoneFiber := {xs : RetryWords // output decode31 xs = none}

@[implicit_reducible] noncomputable def outputNoneFiberFintype : Fintype OutputNoneFiber :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def outputNoneFiberCard : Nat :=
  @Fintype.card OutputNoneFiber outputNoneFiberFintype

theorem firstSome_eq_none_iff (xs : List (Option Value)) :
    firstSome xs = none ↔ ∀ x ∈ xs, x = none := by
  induction xs with
  | nil => simp [firstSome]
  | cons x xs ih =>
      cases x with
      | none => simpa [firstSome] using ih
      | some a => simp [firstSome]

theorem output_decode31_eq_none_iff (xs : RetryWords) :
    output decode31 xs = none ↔ ∀ i, decode31 (xs i) = none := by
  unfold output
  rw [firstSome_eq_none_iff]
  constructor
  · intro hall i
    have hi : decode31 (xs i) ∈ List.ofFn fun j : Fin 16 => decode31 (xs j) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    exact hall _ hi
  · intro hall x hx
    simp only [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact hall i

noncomputable def outputNoneEquivRejectVectors :
    OutputNoneFiber ≃ (Fin 16 → rejectWordFiber) where
  toFun xs i := ⟨xs.1 i, (output_decode31_eq_none_iff xs.1).mp xs.2 i⟩
  invFun f := ⟨fun i => (f i).1, (output_decode31_eq_none_iff _).mpr fun i => (f i).2⟩
  left_inv xs := by apply Subtype.ext; rfl
  right_inv f := by funext i; apply Subtype.ext; rfl

theorem outputNoneFiberCard_eq : outputNoneFiberCard = 2 ^ 16 := by
  letI : Fintype OutputNoneFiber := outputNoneFiberFintype
  letI : Fintype rejectWordFiber := rejectWordFiberFintype
  have heq := Fintype.card_congr outputNoneEquivRejectVectors
  have hword : Fintype.card rejectWordFiber = 2 := by
    simpa [rejectWordFiberCard] using rejectWordFiberCard_eq_two
  calc
    outputNoneFiberCard = Fintype.card (Fin 16 → rejectWordFiber) := by
      simpa [outputNoneFiberCard] using heq
    _ = 2 ^ 16 := by
      rw [Fintype.card_fun, hword]
      simp

#print axioms firstSome_eq_none_iff
#print axioms output_decode31_eq_none_iff
#print axioms outputNoneFiberCard_eq

end M31RetryOutputFiber
