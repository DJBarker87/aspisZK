import M31AcceptFiber
import M31RetryOutputFiber
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

noncomputable def rejectSet : Finset Word :=
  Finset.univ.filter fun w => mask31 w = P31

def rejectWordFiber : Type := {w : Word // decode31 w = none}

@[implicit_reducible] noncomputable def rejectWordFiberFintype : Fintype rejectWordFiber :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def rejectWordFiberCard : Nat :=
  @Fintype.card rejectWordFiber rejectWordFiberFintype

theorem mask31_lt_two31 (w : Word) : mask31 w < 2 ^ 31 := by
  rw [mask31_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem decode31_eq_none_iff (w : Word) : decode31 w = none ↔ mask31 w = P31 := by
  unfold decode31
  by_cases hlt : mask31 w < P31
  · simp only [dif_pos hlt]
    constructor
    · intro h
      cases h
    · intro h
      exact (lt_irrefl _ (h ▸ hlt)).elim
  · simp only [dif_neg hlt]
    constructor
    · intro _
      have hbound := mask31_lt_two31 w
      unfold P31 at hlt ⊢
      omega
    · intro _
      trivial

noncomputable def rejectedValueEquiv : rejectWordFiber ≃ rejectSet where
  toFun x := ⟨x.1, by
    simp only [rejectSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact decode31_eq_none_iff x.1 |>.mp x.2⟩
  invFun x := ⟨x.1, by
    exact (decode31_eq_none_iff x.1).2 (Finset.mem_filter.mp x.2).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem rejectSet_card : rejectSet.card = 2 := by
  let w0 : Word := ⟨P31, by unfold P31; omega⟩
  let w1 : Word := ⟨P31 + 2 ^ 31, by unfold P31; omega⟩
  have hrsmall : P31 < 2 ^ 31 := by unfold P31; omega
  have hmod0 : w0.val % 2 ^ 31 = P31 := by
    change P31 % 2 ^ 31 = P31
    exact Nat.mod_eq_of_lt hrsmall
  have hmod1 : w1.val % 2 ^ 31 = P31 := by
    change (P31 + 2 ^ 31) % 2 ^ 31 = P31
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero]
    exact Nat.mod_eq_of_lt hrsmall
  have hmask0 : mask31 w0 = P31 := by rw [mask31_eq_mod, hmod0]
  have hmask1 : mask31 w1 = P31 := by rw [mask31_eq_mod, hmod1]
  have hneq : w0 ≠ w1 := by
    intro h
    have := congrArg Fin.val h
    simp only [w0, w1, Fin.mk.injEq] at this
    omega
  have hset : rejectSet = {w0, w1} := by
    ext w
    simp only [rejectSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hmask
      have hmod : w.val % 2 ^ 31 = P31 := by
        rw [← mask31_eq_mod]
        exact hmask
      have hdiv : w.val / 2 ^ 31 < 2 := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 31)).2
        have hw := w.isLt
        norm_num at hw ⊢
        omega
      have hdecomp : w.val % 2 ^ 31 + 2 ^ 31 * (w.val / 2 ^ 31) = w.val :=
        Nat.mod_add_div _ _
      have hq : w.val / 2 ^ 31 = 0 ∨ w.val / 2 ^ 31 = 1 := by omega
      rcases hq with hq | hq
      · left
        apply Fin.ext
        rw [← hdecomp, hmod, hq]
        simp [w0]
      · right
        apply Fin.ext
        rw [← hdecomp, hmod, hq]
        simp [w1]
    · intro h
      rcases h with h | h
      · subst w
        exact hmask0
      · subst w
        exact hmask1
  rw [hset]
  simp [hneq]

theorem rejectWordFiberCard_eq_two : rejectWordFiberCard = 2 := by
  letI : Fintype rejectWordFiber := rejectWordFiberFintype
  have hcard := Fintype.card_congr rejectedValueEquiv
  have hset : Fintype.card (rejectSet) = 2 := by
    rw [Fintype.card_coe]
    exact rejectSet_card
  calc
    rejectWordFiberCard = Fintype.card rejectSet := by
      simpa [rejectWordFiberCard] using hcard
    _ = 2 := hset

#print axioms rejectSet_card
#print axioms rejectWordFiberCard_eq_two

end M31RetryOutputFiber
