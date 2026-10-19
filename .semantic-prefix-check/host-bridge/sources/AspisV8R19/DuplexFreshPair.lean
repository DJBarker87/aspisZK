import AspisV8R17.AdaptiveOracle

/-! Both cells are fixed by the prefix; the advance address is NOT selected
from the squeeze answer. Repeated/prior-read addresses are explicitly excluded.
This finite-oracle theorem is not yet the source experiment's joint law. -/
set_option autoImplicit false
namespace AspisV8R19.DuplexFreshPair
open AspisV8R17.AdaptiveOracle
variable {I A : Type*} [DecidableEq I]

def pairEquiv (i j : I) (e f : A ≃ A) : (I → A) ≃ (I → A) :=
  (cellEquiv i e).trans (cellEquiv j f)

theorem pair_at_first (i j : I) (hne : i ≠ j) (e f : A ≃ A) (H : I → A) :
    pairEquiv i j e f H i = e (H i) := by
  simp [pairEquiv, cellEquiv, hne]

theorem pair_at_second (i j : I) (hne : i ≠ j) (e f : A ≃ A) (H : I → A) :
    pairEquiv i j e f H j = f (H j) := by
  simp [pairEquiv, cellEquiv, Ne.symm hne]

theorem pair_preserves_trace (next : List (I × A) → I) (H : I → A) (n : ℕ)
    (i j : I) (e f : A ≃ A)
    (hi : ∀ p ∈ run next H n [], p.1 ≠ i)
    (hj : ∀ p ∈ run next H n [], p.1 ≠ j) :
    run next (pairEquiv i j e f H) n [] = run next H n [] := by
  apply run_congr_on_reads
  intro p hp
  simp [pairEquiv, cellEquiv, hi p hp, hj p hp]

def tracePairFiberEquiv (next : List (I × A) → I) (n : ℕ)
    (tr : List (I × A)) (i j : I) (hne : i ≠ j)
    (hi : ∀ p ∈ tr, p.1 ≠ i) (hj : ∀ p ∈ tr, p.1 ≠ j)
    (e f : A ≃ A) (a b : A) :
    {H : I → A // run next H n [] = tr ∧ H i = a ∧ H j = b} ≃
    {H : I → A // run next H n [] = tr ∧ H i = e a ∧ H j = f b} where
  toFun H := ⟨pairEquiv i j e f H.val, by
    refine ⟨?_, ?_, ?_⟩
    · exact (pair_preserves_trace next H.val n i j e f
        (by simpa [H.property.1] using hi) (by simpa [H.property.1] using hj)).trans H.property.1
    · rw [pair_at_first i j hne, H.property.2.1]
    · rw [pair_at_second i j hne, H.property.2.2]⟩
  invFun H := ⟨(pairEquiv i j e f).symm H.val, by
    have heq : (pairEquiv i j e f).symm H.val = pairEquiv j i f.symm e.symm H.val := rfl
    rw [heq]
    refine ⟨?_, ?_, ?_⟩
    · exact (pair_preserves_trace next H.val n j i f.symm e.symm
        (by simpa [H.property.1] using hj) (by simpa [H.property.1] using hi)).trans H.property.1
    · rw [pair_at_second j i hne.symm, H.property.2.1, e.symm_apply_apply]
    · rw [pair_at_first j i hne.symm, H.property.2.2, f.symm_apply_apply]⟩
  left_inv H := by apply Subtype.ext; exact (pairEquiv i j e f).symm_apply_apply H.val
  right_inv H := by apply Subtype.ext; exact (pairEquiv i j e f).apply_symm_apply H.val

theorem fresh_pair_counts_equal [Fintype I] [Fintype A] [DecidableEq A]
    (next : List (I × A) → I) (n : ℕ) (tr : List (I × A))
    (i j : I) (hne : i ≠ j) (hi : ∀ p ∈ tr, p.1 ≠ i)
    (hj : ∀ p ∈ tr, p.1 ≠ j) (a b c d : A) :
    AspisV8Privacy.fiberCount (fun H : I → A => (run next H n [], H i, H j)) (tr,a,b) =
    AspisV8Privacy.fiberCount (fun H : I → A => (run next H n [], H i, H j)) (tr,c,d) := by
  classical
  unfold AspisV8Privacy.fiberCount
  simp only [Fintype.card_eq_nat_card]
  let left : {H : I → A // (run next H n [], H i, H j) = (tr,a,b)} ≃
      {H : I → A // run next H n [] = tr ∧ H i = a ∧ H j = b} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [Prod.mk.injEq])
  let right : {H : I → A // (run next H n [], H i, H j) = (tr,c,d)} ≃
      {H : I → A // run next H n [] = tr ∧ H i = c ∧ H j = d} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [Prod.mk.injEq])
  apply Nat.card_congr
  exact left.trans ((tracePairFiberEquiv next n tr i j hne hi hj
    (Equiv.swap a c) (Equiv.swap b d) a b).trans
      ((Equiv.subtypeEquivRight (fun _ => by simp)).trans right.symm))

theorem fresh_pair_probabilities [Fintype I] [Fintype A] [Nonempty A] [DecidableEq A]
    (next : List (I × A) → I) (n : ℕ) (tr : List (I × A))
    (i j : I) (hne : i ≠ j) (hi : ∀ p ∈ tr, p.1 ≠ i)
    (hj : ∀ p ∈ tr, p.1 ≠ j) (a b c d : A) :
    AspisV8Privacy.uniformProbability (fun H : I → A => (run next H n [], H i, H j)) (tr,a,b) =
    AspisV8Privacy.uniformProbability (fun H : I → A => (run next H n [], H i, H j)) (tr,c,d) := by
  unfold AspisV8Privacy.uniformProbability
  rw [fresh_pair_counts_equal next n tr i j hne hi hj a b c d]

#print axioms pairEquiv
#print axioms pair_at_first
#print axioms pair_at_second
#print axioms pair_preserves_trace
#print axioms tracePairFiberEquiv
#print axioms fresh_pair_counts_equal
#print axioms fresh_pair_probabilities
end AspisV8R19.DuplexFreshPair
