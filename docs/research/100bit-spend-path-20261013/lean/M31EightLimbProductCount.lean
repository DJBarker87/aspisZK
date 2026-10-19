import M31RetryOutputFiber
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import M31RetryFiberNatCardBridge

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev RetryInput := Fin 16 → Word
abbrev EightRetryInputs := Fin 8 → RetryInput
abbrev EightValues := Fin 8 → Value

/-- Exact block-output fiber: eight independent fixed-window retries are
run on eight independent 16-word blocks. -/
abbrev eightOutputFiber (ys : EightValues) :=
  {xs : EightRetryInputs // ∀ i : Fin 8, output decode31 (xs i) = some (ys i)}

@[reducible] noncomputable def eightOutputFiberCard (ys : EightValues) : Nat :=
  Nat.card (eightOutputFiber ys)

/-- Independent block fibers are exactly the dependent product of their
single-block fibers. This records the independence assumption as product input
space structure, rather than assuming independent outputs. -/
def eightOutputFiberEquiv (ys : EightValues) :
    eightOutputFiber ys ≃ ((i : Fin 8) → outputFiber decode31 (ys i)) where
  toFun xs i := ⟨xs.1 i, xs.2 i⟩
  invFun fs := ⟨fun i => (fs i).1, fun i => (fs i).2⟩
  left_inv xs := by apply Subtype.ext; rfl
  right_inv fs := by funext i; apply Subtype.ext; rfl

theorem eightOutputFiberCard_eq_prod (ys : EightValues) :
    eightOutputFiberCard ys = ∏ i : Fin 8, outputFiberCard decode31 (ys i) := by
  classical
  calc
    eightOutputFiberCard ys =
        Nat.card ((i : Fin 8) → outputFiber decode31 (ys i)) := by
      simp only [eightOutputFiberCard]
      exact Nat.card_congr (eightOutputFiberEquiv ys)
    _ = ∏ i : Fin 8, Nat.card (outputFiber decode31 (ys i)) := by
      rw [Nat.card_pi]
    _ = ∏ i : Fin 8, outputFiberCard decode31 (ys i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact natFiberCard_eq_outputFiberCard (ys i)

/-- Since every accepted residue has the same fixed-window fiber, every
accepted eight-limb tuple has the same number of independent word-block
preimages. -/
theorem eightOutputFiberCard_constant (ys zs : EightValues) :
    eightOutputFiberCard ys = eightOutputFiberCard zs := by
  rw [eightOutputFiberCard_eq_prod, eightOutputFiberCard_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact outputFiber_card_eq (ys i) (zs i)

#print axioms eightOutputFiberCard_eq_prod
#print axioms eightOutputFiberCard_constant

end M31RetryOutputFiber
