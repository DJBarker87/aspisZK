import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! Symbolic support selection. We use a threshold incidence bound rather
than a large generated convexity certificate. No received curve/candidate
membership is assumed. -/
set_option autoImplicit false
namespace AspisV8.NearGammaSupport
open Finset
variable {J X : Type*} [DecidableEq J] [DecidableEq X]

def load (S : Finset J) (A : J → Finset X) (x : X) : Finset J :=
  S.filter fun j => x ∈ A j

theorem subset_count (S : Finset J) (A : J → Finset X) (x : X) (r : ℕ) :
    ((S.powersetCard r).filter fun I => ∀ j ∈ I, x ∈ A j).card =
      (load S A x).card.choose r := by
  have he : (S.powersetCard r).filter (fun I => ∀ j ∈ I, x ∈ A j) =
      (load S A x).powersetCard r := by
    ext I
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hcard⟩,h⟩
      exact ⟨fun j hj => mem_filter.mpr ⟨hsub hj,h j hj⟩,hcard⟩
    · rintro ⟨hsub,hcard⟩
      exact ⟨⟨fun j hj => (mem_filter.mp (hsub hj)).1,hcard⟩,
        fun j hj => (mem_filter.mp (hsub hj)).2⟩
  rw [he, card_powersetCard]

/-- Many high-load positions force an r-subset with large common support. -/
theorem common_of_high_load (S : Finset J) (D H : Finset X)
    (A : J → Finset X) (r h target : ℕ) (hHD : H ⊆ D)
    (hh : ∀ x ∈ H, h ≤ (load S A x).card)
    (cert : target * S.card.choose r < H.card * h.choose r) :
    ∃ I ∈ S.powersetCard r,
      target < (D.filter fun x => ∀ j ∈ I, x ∈ A j).card := by
  classical
  by_contra hn
  push Not at hn
  have hc := Finset.card_nsmul_le_card_nsmul (R := Nat)
    (s := H) (t := S.powersetCard r)
    (fun x I => ∀ j ∈ I, x ∈ A j)
    (m := h.choose r) (n := target)
    (by
      intro x hx
      change h.choose r ≤ ((S.powersetCard r).filter _).card
      rw [subset_count]
      exact Nat.choose_le_choose r (hh x hx))
    (by
      intro I hi
      change (H.filter _).card ≤ target
      exact (card_le_card (filter_subset_filter _ hHD)).trans (hn I hi))
  rw [card_powersetCard] at hc
  simp only [nsmul_eq_mul] at hc
  exact Nat.not_lt_of_ge (by simpa [Nat.mul_comm] using hc) cert

/-- A missing-incidence bound supplies the high-load set. -/
theorem low_load_bound (S : Finset J) (D : Finset X) (A : J → Finset X)
    (h B : ℕ) (hm : h ≤ S.card)
    (near : ∀ j ∈ S, (D \ A j).card ≤ B) :
    (D.filter fun x => (load S A x).card < h).card * (S.card-h+1) ≤ S.card*B := by
  classical
  have hc := Finset.card_nsmul_le_card_nsmul (R := Nat)
    (s := D.filter fun x => (load S A x).card < h) (t := S)
    (fun x j => x ∉ A j)
    (by
      intro x hx
      change S.card-h+1 ≤ (S.filter fun j => x ∉ A j).card
      have ht := card_filter_add_card_filter_not (s := S) (fun j => x ∈ A j)
      have hx' := (mem_filter.mp hx).2
      change (S.filter fun j => x ∈ A j).card < h at hx'
      omega)
    (by
      intro j hj
      change ((D.filter _).filter fun x => x ∉ A j).card ≤ B
      apply le_trans (card_le_card ?_) (near j hj)
      intro x hx
      exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩)
  simp only [nsmul_eq_mul] at hc
  change (D.filter fun x => (load S A x).card < h).card * (S.card-h+1) ≤ S.card*B at hc
  exact hc

/-- Concrete sizes only enter this final sparse arithmetic certificate.
The binomial values remain parameters in the symbolic combinatorial proof. -/
theorem common_64_29 (S : Finset J) (D : Finset X) (A : J → Finset X)
    (hS : S.card = 64) (hD : D.card = 262144)
    (near : ∀ j ∈ S, (D \ A j).card ≤ 9301)
    (cert : 9557 * Nat.choose 64 29 < 113328 * Nat.choose 61 29) :
    ∃ I ∈ S.powersetCard 29,
      9557 < (D.filter fun x => ∀ j ∈ I, x ∈ A j).card := by
  classical
  let H := D.filter fun x => 61 ≤ (load S A x).card
  have low := low_load_bound S D A 61 9301 (by omega) near
  have split := card_filter_add_card_filter_not (s := D) (fun x => 61 ≤ (load S A x).card)
  have hc : 113328 ≤ H.card := by
    simp only [hS] at low
    simp only [not_le] at split
    rw [hD] at split
    dsimp [H]
    omega
  refine common_of_high_load S D H A 29 61 9557 (filter_subset _ _) ?_ ?_
  · exact fun x hx => (mem_filter.mp hx).2
  · rw [hS]
    exact cert.trans_le (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (Nat.choose 61 29) hc)

#print axioms subset_count
#print axioms common_of_high_load
#print axioms low_load_bound
#print axioms common_64_29
end AspisV8.NearGammaSupport
