import R0C.Counting
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Basic

/-! Abstract counting of ordered injections into a fixed subset. Applying
this to R417 turns its successful ordered marginal into the set-containment
ratio needed by the opening argument, without conditioning away errors. -/
set_option autoImplicit false
namespace R0C.QueryCounting
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Ordered (q : Nat) (A : Type) := {f : Fin q → A // Function.Injective f}

def embeddingEquiv (q : Nat) (A : Type) : Ordered q A ≃ (Fin q ↪ A) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl

theorem ordered_card (q : Nat) (A : Type) [Fintype A] :
    Fintype.card (Ordered q A) = (Fintype.card A).descFactorial q := by
  rw [Fintype.card_congr (embeddingEquiv q A), Fintype.card_embedding_eq, Fintype.card_fin]

def restrictedEquiv {q : Nat} {A : Type} [DecidableEq A] (M : Finset A) :
    {f : Ordered q A // ∀ i, f.val i ∈ M} ≃ (Fin q ↪ ↥M) where
  toFun f := ⟨fun i => ⟨f.val.val i, f.property i⟩,
    fun i j h => f.val.property (congrArg Subtype.val h)⟩
  invFun f := ⟨⟨fun i => (f i).val,
    fun i j h => f.injective (Subtype.ext h)⟩, fun i => (f i).property⟩
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl

theorem restricted_card (q : Nat) {A : Type} [Fintype A] [DecidableEq A]
    (M : Finset A) :
    Fintype.card {f : Ordered q A // ∀ i, f.val i ∈ M} = M.card.descFactorial q := by
  rw [Fintype.card_congr (restrictedEquiv M), Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_coe]

theorem subset_mean (q : Nat) {A : Type} [Fintype A] [DecidableEq A]
    [Fintype (Ordered q A)]
    (M : Finset A) :
    mean (fun f : Ordered q A => indicator (∀ i, f.val i ∈ M)) =
      (M.card.choose q : ℚ) / (Fintype.card A).choose q := by
  have hc : Nat.card {f : Ordered q A // ∀ i, f.val i ∈ M} = M.card.descFactorial q := by
    rw [Nat.card_congr (restrictedEquiv M), Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
  have ho : Nat.card (Ordered q A) = (Fintype.card A).descFactorial q := by
    rw [Nat.card_congr (embeddingEquiv q A), Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq, Fintype.card_fin]
  rw [Counting.mean_indicator_card]
  simp only [← Nat.card_eq_fintype_card]
  rw [hc, ho,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Nat.cast_mul]
  have hq : (q.factorial : ℚ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  simpa only [Nat.card_eq_fintype_card] using (mul_div_mul_left (M.card.choose q : ℚ)
    ((Fintype.card A).choose q : ℚ) hq)

#print axioms ordered_card
#print axioms restricted_card
#print axioms subset_mean
end
end R0C.QueryCounting
