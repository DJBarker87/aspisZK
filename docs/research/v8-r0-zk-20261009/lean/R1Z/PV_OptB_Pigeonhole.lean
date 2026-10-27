import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Pigeonhole

/-- A possible exact counterexample route: a public root has too few values
to fix every small private-coordinate set. This lemma alone does not install
an admitted witness family, copy-row extraction, or a reached native fault. -/
theorem distinct_small_sets {A Public : Type} [Fintype A] [Fintype Public]
    (n k : Nat) (pub : (Fin n → A) → Public)
    (values : (Fin n → A) → Fin n → Finset A)
    (contains : ∀ w i, w i ∈ values w i)
    (bounded : ∀ w i, (values w i).card ≤ k)
    (large : Fintype.card Public * k^n < Fintype.card A ^ n) :
    ∃ w u, pub w = pub u ∧ values w ≠ values u := by
  classical
  by_contra absent
  have stable : ∀ w u, pub w = pub u → values w = values u := by
    intro w u same
    by_contra different
    exact absent ⟨w,u,same,different⟩
  let sets := fun p i =>
    if existsWitness : ∃ w, pub w = p then values (Classical.choose existsWitness) i else ∅
  have sets_bound : ∀ p i, (sets p i).card ≤ k := by
    intro p i
    dsimp only [sets]
    split_ifs with existsWitness
    · exact bounded _ _
    · simp
  have belongs : ∀ w i, w i ∈ sets (pub w) i := by
    intro w i
    dsimp only [sets]
    rw [dif_pos ⟨w,rfl⟩]
    have same := stable w (Classical.choose (show ∃ u, pub u = pub w from ⟨w,rfl⟩))
      (Classical.choose_spec (show ∃ u, pub u = pub w from ⟨w,rfl⟩)).symm
    rw [← same]
    exact contains w i
  let code : (Fin n → A) → Σ p : Public, ∀ i : Fin n, {a : A // a ∈ sets p i} :=
    fun w => ⟨pub w,fun i => ⟨w i,belongs w i⟩⟩
  have injective : Function.Injective code := by
    intro w u same
    exact congrArg (fun z : Σ p : Public, ∀ i : Fin n, {a : A // a ∈ sets p i} =>
      fun i => (z.2 i).val) same
  have small : Fintype.card (Fin n → A) ≤ Fintype.card Public * k^n := by
    calc
      _ ≤ Fintype.card (Σ p : Public, ∀ i : Fin n, {a : A // a ∈ sets p i}) :=
        Fintype.card_le_of_injective code injective
      _ = ∑ p : Public, ∏ i : Fin n, (sets p i).card := by simp
      _ ≤ ∑ _p : Public, ∏ _i : Fin n, k := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.prod_le_prod' (fun i _ => sets_bound p i)
      _ = Fintype.card Public * k^n := by simp
  have cards : Fintype.card (Fin n → A) = Fintype.card A ^ n := by simp
  rw [cards] at small
  exact (not_lt_of_ge small) large

#print axioms distinct_small_sets
end R1Z.PV_OptB_Pigeonhole
