import NearGammaSupport

/-! Support averaging with a discrete binomial tangent. The family of
supports may be arbitrary; no code or candidate premise occurs here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
namespace AspisV8.HighAgreementTail
open Finset

/-- Pascal telescoping keeps binomial evaluation symbolic. -/
theorem choose_add_succ (n d r : Nat) :
    (n+d).choose (r+1)=n.choose (r+1)+∑ j∈Finset.range d, (n+j).choose r := by
  induction d with
  | zero => simp only [Nat.add_zero,Finset.range_zero,Finset.sum_empty]
  | succ d ih =>
      rw [Nat.add_succ,Nat.choose_succ_succ,ih,Finset.sum_range_succ]
      omega

/-- Global integer tangent for the discretely convex binomial sequence. -/
theorem choose_tangent (h m r : Nat) :
    h.choose (r+1)+m*h.choose r ≤ m.choose (r+1)+h*h.choose r := by
  rcases le_total h m with hm | mh
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
    have lower : d*h.choose r ≤ ∑ j∈Finset.range d, (h+j).choose r := by
      calc
        d*h.choose r = ∑ _j∈Finset.range d, h.choose r := by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
        _ ≤ _ := Finset.sum_le_sum fun j _ => Nat.choose_le_choose r (by omega)
    rw [choose_add_succ]
    nlinarith
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le mh
    have upper : (∑ j∈Finset.range d, (m+j).choose r) ≤ d*(m+d).choose r := by
      calc
        _ ≤ ∑ _j∈Finset.range d, (m+d).choose r := Finset.sum_le_sum (by
          intro j hj
          exact Nat.choose_le_choose r (by have small := Finset.mem_range.mp hj; omega))
        _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
    rw [choose_add_succ]
    nlinarith

variable {J X : Type*} [DecidableEq J] [DecidableEq X]

theorem choose_sum_lower (D : Finset X) (f : X → Nat) (h r : Nat)
    (mass : h*D.card ≤ ∑ x∈D, f x) :
    D.card*h.choose (r+1) ≤ ∑ x∈D, (f x).choose (r+1) := by
  have tangent := Finset.sum_le_sum (s := D) (fun x _ => choose_tangent h (f x) r)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,
    ← Finset.sum_mul] at tangent
  have weighted := Nat.mul_le_mul_right (h.choose r) mass
  nlinarith

/-- New information from average load, stronger than the earlier coarse
high-load threshold split, reusing its exact subset-count identity. -/
theorem common_of_average_load (S : Finset J) (D : Finset X)
    (A : J → Finset X) (r h target : Nat)
    (mass : h*D.card ≤ ∑ x∈D, (NearGammaSupport.load S A x).card)
    (cert : target*S.card.choose (r+1)<D.card*h.choose (r+1)) :
    ∃ I∈S.powersetCard (r+1),
      target<(D.filter fun x => ∀ j∈I, x∈A j).card := by
  classical
  by_contra noCommon
  push Not at noCommon
  have lower := choose_sum_lower D (fun x => (NearGammaSupport.load S A x).card) h r mass
  have double := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun x I => ∀ j∈I, x∈A j) (s := D) (t := S.powersetCard (r+1))
  change (∑ x∈D, ((S.powersetCard (r+1)).filter fun I => ∀ j∈I, x∈A j).card)=
    ∑ I∈S.powersetCard (r+1), (D.filter fun x => ∀ j∈I, x∈A j).card at double
  simp only [NearGammaSupport.subset_count] at double
  rw [double] at lower
  have upper := Finset.sum_le_sum noCommon
  simp only [Finset.sum_const,Finset.card_powersetCard,nsmul_eq_mul,Nat.cast_id] at upper
  nlinarith

theorem incidence_lower (S : Finset J) (D : Finset X) (A : J → Finset X)
    (t : Nat) (inside : ∀ j∈S, A j⊆D) (large : ∀ j∈S, t≤(A j).card) :
    S.card*t ≤ ∑ x∈D, (NearGammaSupport.load S A x).card := by
  have double := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun j x => x∈A j) (s := S) (t := D)
  change (∑ j∈S, (D.filter fun x => x∈A j).card)=
    ∑ x∈D, (NearGammaSupport.load S A x).card at double
  rw [← double]
  calc
    S.card*t = ∑ _j∈S, t := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
    _ ≤ _ := Finset.sum_le_sum (by
      intro j hj
      have equal : D.filter (fun x => x∈A j)=A j := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2,fun hx => ⟨inside j hj hx,hx⟩⟩
      rw [equal]
      exact large j hj)

/-- Four-term descending products, not Pascal expansion at n=128. -/
theorem selected_certificate :
    9557*Nat.choose 128 4<262144*Nat.choose 57 4 := by
  rw [Nat.choose_eq_descFactorial_div_factorial,
    Nat.choose_eq_descFactorial_div_factorial]
  decide

theorem common_128_4 (S : Finset J) (D : Finset X) (A : J → Finset X)
    (hS : S.card=128) (hD : D.card=262144)
    (inside : ∀ j∈S, A j⊆D) (large : ∀ j∈S, 117965≤(A j).card) :
    ∃ I∈S.powersetCard 4, 9557<(D.filter fun x => ∀ j∈I, x∈A j).card := by
  have incidence := incidence_lower S D A 117965 inside large
  apply common_of_average_load S D A 3 57 9557
  · rw [hS] at incidence
    rw [hD]
    omega
  · rw [hS,hD]
    simpa only [Nat.reduceAdd] using selected_certificate

/-- If every four-support intersection has fewer than9558 fibres, at most
127 supports reach117965 fibres. This is a cardinality theorem, not a query law. -/
theorem no_four_large_card_le (S : Finset J) (D : Finset X) (A : J → Finset X)
    (hD : D.card=262144)
    (inside : ∀ j∈S, A j⊆D) (large : ∀ j∈S, 117965≤(A j).card)
    (noFour : ∀ I∈S.powersetCard 4,
      (D.filter fun x => ∀ j∈I, x∈A j).card≤9557) : S.card≤127 := by
  by_contra notSmall
  obtain ⟨selected,subset,card⟩ := Finset.exists_subset_card_eq (show 128≤S.card by omega)
  obtain ⟨I,hI,common⟩ := common_128_4 selected D A card hD
    (fun j hj => inside j (subset hj)) (fun j hj => large j (subset hj))
  have member : I∈S.powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨(Finset.mem_powersetCard.mp hI).1.trans subset,
      (Finset.mem_powersetCard.mp hI).2⟩
  exact Nat.not_lt_of_ge (noFour I member) common

#print axioms choose_add_succ
#print axioms choose_tangent
#print axioms choose_sum_lower
#print axioms common_of_average_load
#print axioms incidence_lower
#print axioms selected_certificate
#print axioms common_128_4
#print axioms no_four_large_card_le
end AspisV8.HighAgreementTail
