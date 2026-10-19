import M31EightLimbProductCount
import M31RetryOutputMassNat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev OneSuccessInput := {xs : RetryInput // ∃ r : Value, output decode31 xs = some r}
abbrev EightSuccessInput := {xs : EightRetryInputs //
  ∀ i : Fin 8, ∃ r : Value, output decode31 (xs i) = some r}

/-- A successful scalar retry is the disjoint union of its exact accepted
output fibers. -/
def zeroValue : Value := ⟨0, by norm_num [P31]⟩

def canonicalOutput (xs : RetryInput) : Value := (output decode31 xs).getD zeroValue

def oneSuccessInputEquiv : OneSuccessInput ≃ (Σ r : Value, outputFiber decode31 r) where
  toFun x := by
    let r := canonicalOutput x.1
    have hr : output decode31 x.1 = some r := by
      rcases x.2 with ⟨s, hs⟩
      dsimp [r, canonicalOutput]
      rw [hs]
      rfl
    exact ⟨r, ⟨x.1, hr⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨r, ⟨xs, hxs⟩⟩
    have hc : canonicalOutput xs = r := by
      dsimp [canonicalOutput]
      rw [hxs]
      rfl
    change Sigma.mk (β := fun r : Value => outputFiber decode31 r) (canonicalOutput xs)
        (⟨xs, (by rw [hc]; exact hxs)⟩ : outputFiber decode31 (canonicalOutput xs)) =
      Sigma.mk (β := fun r : Value => outputFiber decode31 r) r
        (⟨xs, hxs⟩ : outputFiber decode31 r)
    have hsub : HEq
        (⟨xs, (by rw [hc]; exact hxs)⟩ : outputFiber decode31 (canonicalOutput xs))
        (⟨xs, hxs⟩ : outputFiber decode31 r) := by
      cases hc
      exact HEq.rfl
    exact Sigma.ext hc hsub

theorem oneSuccessInput_card : Nat.card OneSuccessInput = natOutputMass := by
  classical
  calc
    Nat.card OneSuccessInput = Nat.card (Σ r : Value, outputFiber decode31 r) :=
      Nat.card_congr oneSuccessInputEquiv
    _ = ∑ r : Value, Nat.card (outputFiber decode31 r) := Nat.card_sigma
    _ = natOutputMass := by
      unfold natOutputMass
      apply Finset.sum_congr rfl
      intro r hr
      have hnat : Nat.card (outputFiber decode31 r) = outputFiberCard decode31 r := by
        letI : Fintype (outputFiber decode31 r) := outputFiberFintype decode31 r
        change Nat.card (outputFiber decode31 r) =
          @Fintype.card (outputFiber decode31 r) (outputFiberFintype decode31 r)
        exact Nat.card_eq_fintype_card
      exact hnat.trans (natFiberCard_eq_outputFiberCard r).symm

theorem oneSuccessInput_card_exact :
    Nat.card OneSuccessInput = (2 ^ 32) ^ 16 - 2 ^ 16 := by
  rw [oneSuccessInput_card]
  exact natOutputMass_eq_success_count

def eightSuccessInputEquiv :
    EightSuccessInput ≃ ((i : Fin 8) → OneSuccessInput) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun fs := ⟨fun i => (fs i).1, fun i => (fs i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv fs := by funext i; apply Subtype.ext; rfl

theorem eightSuccessInput_card_exact :
    Nat.card EightSuccessInput = ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 := by
  classical
  calc
    Nat.card EightSuccessInput =
        Nat.card ((i : Fin 8) → OneSuccessInput) := Nat.card_congr eightSuccessInputEquiv
    _ = ∏ i : Fin 8, Nat.card OneSuccessInput := Nat.card_pi
    _ = ∏ _i : Fin 8, ((2 ^ 32) ^ 16 - 2 ^ 16) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [oneSuccessInput_card_exact]
    _ = ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 := by simp

/-- The complete input tape for eight independent M31 limbs has exact size
`((2^32)^16)^8`; its all-success subset has the exact eighth power of the
single-limb success count. -/
theorem eightRetryInput_card :
    Nat.card EightRetryInputs = ((2 ^ 32) ^ 16) ^ 8 := by
  classical
  calc
    Nat.card EightRetryInputs = ∏ _i : Fin 8, Nat.card RetryInput := Nat.card_pi
    _ = ∏ _i : Fin 8, ((2 ^ 32) ^ 16) := by
      apply Finset.prod_congr rfl
      intro i hi
      change Nat.card (Fin 16 → Word) = _
      rw [Nat.card_fun]
      simp [Nat.card_fin]
    _ = ((2 ^ 32) ^ 16) ^ 8 := by simp

#print axioms oneSuccessInput_card_exact
#print axioms eightSuccessInput_card_exact
#print axioms eightRetryInput_card

end M31RetryOutputFiber
