import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! Private extractor samples, not verifier queries. A factorial-moment
double count bounds ANY accepted failure set contained in samples with at
least r errors from a fixed bad support. No conditional-on-acceptance
uniformity is assumed. The support must be fixed before the private sample.
The Gao/source bridge supplying the failure implication is separate. -/
set_option autoImplicit false
namespace AspisV8.PrivateSampleMoment
open Finset
variable {F : Type*} [DecidableEq F]

theorem witnesses (bad S : Finset F) (t : Nat) :
    ((bad.powersetCard t).filter fun W => W ⊆ S).card =
      (S ∩ bad).card.choose t := by
  have eq : (bad.powersetCard t).filter (fun W => W ⊆ S) =
      (S ∩ bad).powersetCard t := by
    ext W
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hb,hc⟩,hs⟩
      exact ⟨subset_inter hs hb,hc⟩
    · rintro ⟨h,hc⟩
      exact ⟨⟨h.trans inter_subset_right,hc⟩,h.trans inter_subset_left⟩
  rw [eq,card_powersetCard]

/-- The failure set may include arbitrary further acceptance/strategy
restrictions. This proves an unconditional upper bound on its mass under a
fresh uniform sample; it does not say samples stay uniform after acceptance. -/
theorem failure_count (U bad : Finset F) (m r t : Nat)
    (badSubset : bad ⊆ U) (tm : t ≤ m)
    (failures : Finset (Finset F))
    (samples : failures ⊆ U.powersetCard m)
    (many : ∀ S ∈ failures, r ≤ (S ∩ bad).card) :
    failures.card * r.choose t ≤
      bad.card.choose t * (U.card-t).choose (m-t) := by
  have h := Finset.card_nsmul_le_card_nsmul (R := Nat)
    (s := failures) (t := bad.powersetCard t) (fun S W => W ⊆ S)
    (m := r.choose t) (n := (U.card-t).choose (m-t))
    (by
      intro S hS
      change r.choose t ≤ ((bad.powersetCard t).filter _).card
      rw [witnesses]
      exact Nat.choose_le_choose t (many S hS))
    (by
      intro W hW
      change (failures.filter fun S => W ⊆ S).card ≤ _
      have hWU := (mem_powersetCard.mp hW).1.trans badSubset
      have hcard := (mem_powersetCard.mp hW).2
      have hwm : W.card ≤ m := by simpa only [hcard] using tm
      calc
        (failures.filter fun S => W ⊆ S).card ≤
          ((U.powersetCard m).filter fun S => W ⊆ S).card :=
            card_le_card (filter_subset_filter _ samples)
        _ = (U.card-t).choose (m-t) := by
          rw [card_filter_powersetCard_subset W U m hWU hwm,hcard])
  simpa only [nsmul_eq_mul,card_powersetCard,Nat.cast_id] using h

def ceiling (T B m r t : Nat) : ℚ :=
  (B.choose t * (T-t).choose (m-t) : Nat) /
    (T.choose m * r.choose t : Nat)

theorem failure_probability (U bad : Finset F) (m r t : Nat)
    (badSubset : bad ⊆ U) (tm : t ≤ m) (tr : t ≤ r) (mT : m ≤ U.card)
    (failures : Finset (Finset F))
    (samples : failures ⊆ U.powersetCard m)
    (many : ∀ S ∈ failures, r ≤ (S ∩ bad).card) :
    (failures.card : ℚ) / U.card.choose m ≤ ceiling U.card bad.card m r t := by
  have posT : (0:ℚ) < U.card.choose m := by exact_mod_cast Nat.choose_pos mT
  have posR : (0:ℚ) < r.choose t := by exact_mod_cast Nat.choose_pos tr
  have h : (failures.card : ℚ) * r.choose t ≤
      bad.card.choose t * (U.card-t).choose (m-t) := by
    exact_mod_cast failure_count U bad m r t badSubset tm failures samples many
  unfold ceiling
  push_cast
  apply (div_le_iff₀ posT).mpr
  have heq : (bad.card.choose t * (U.card-t).choose (m-t) : ℚ) /
      (U.card.choose m * r.choose t) * U.card.choose m =
      (bad.card.choose t * (U.card-t).choose (m-t) : ℚ) / r.choose t := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ posR).mpr h

/-- A larger fixed support cap only increases this bound. -/
theorem ceiling_mono_bad (T B B' m r t : Nat) (h : B ≤ B') :
    ceiling T B m r t ≤ ceiling T B' m r t := by
  unfold ceiling
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.mul_le_mul_right ((T-t).choose (m-t)) (Nat.choose_le_choose t h)

/-- Selected extractor parameters. This is a PRIVATE 513-fibre sample, not
an increase from q22 and not evidence that a Merkle root supplies those reads. -/
theorem selected_accepted_failure (U bad : Finset F)
    (domain : U.card = 262144) (badSubset : bad ⊆ U) (badCap : bad.card ≤ 16535)
    (accept fails : Finset F → Prop) [DecidablePred accept] [DecidablePred fails]
    (decoder : ∀ S ∈ U.powersetCard 513, fails S → 129 ≤ (S ∩ bad).card) :
    ((((U.powersetCard 513).filter fun S => accept S ∧ fails S).card : Nat) : ℚ) /
        U.card.choose 513 ≤ ceiling 262144 16535 513 129 104 := by
  have h := failure_probability U bad 513 129 104 badSubset (by omega)
    (by omega) (by omega)
    ((U.powersetCard 513).filter fun S => accept S ∧ fails S)
    (filter_subset _ _) (by
      intro S hS
      exact decoder S (mem_filter.mp hS).1 (mem_filter.mp hS).2.2)
  rw [domain] at h
  rw [domain]
  exact h.trans (ceiling_mono_bad 262144 bad.card 16535 513 129 104 badCap)

#print axioms witnesses
#print axioms failure_count
#print axioms failure_probability
#print axioms ceiling_mono_bad
#print axioms selected_accepted_failure
end AspisV8.PrivateSampleMoment
