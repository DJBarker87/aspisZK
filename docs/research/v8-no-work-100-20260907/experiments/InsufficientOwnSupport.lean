import FixedTargetQuerySupport

/-! Joint fixed-tuple event count with a charged common-schedule branch.
The tuple residuals, denominators, common support and gamma exception set
are fixed before gamma/alpha. The supported event itself can select finals
after alpha. Pole schedules are rejected by an explicit event premise.
No bare all-common query tail is left uncharged.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.InsufficientOwnSupport
open Polynomial Finset
open AspisV8.FixedTargetQuerySupport
noncomputable section
variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

def pairCount (G A : Finset K) (event : Finset I → K → K → Prop) (S : Finset I) : Nat := by
  classical
  exact ∑ g ∈ G, (A.filter fun a => event S g a).card

def totalCount (U : Finset I) (q : Nat) (G A : Finset K)
    (event : Finset I → K → K → Prop) : Nat :=
  ∑ S ∈ U.powersetCard q, pairCount G A event S

theorem pairCount_zero (G A : Finset K) (event : Finset I → K → K → Prop)
    (S : Finset I) (absent : ∀ g ∈ G, ∀ a ∈ A, ¬ event S g a) :
    pairCount G A event S = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro g member
  have empty : A.filter (fun a => event S g a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a hit
    exact absent g member a (Finset.mem_filter.mp hit).1 (Finset.mem_filter.mp hit).2
  rw [empty, Finset.card_empty]

/-- The exception E may be selected from the fixed tuple, but cannot be
chosen retrospectively from g. No relation between E and A is assumed. -/
theorem common_pair_count (G A E : Finset K) (event : Finset I → K → K → Prop)
    (S : Finset I) (forces : ∀ g ∈ G, ∀ a ∈ A, event S g a → g ∈ E) :
    pairCount G A event S ≤ E.card * A.card := by
  classical
  calc
    _ ≤ ∑ g ∈ G, if g ∈ E then A.card else 0 := by
      apply Finset.sum_le_sum
      intro g member
      by_cases inside : g ∈ E
      · rw [if_pos inside]
        exact Finset.card_filter_le _ _
      · rw [if_neg inside]
        have empty : A.filter (fun a => event S g a) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a hit
          exact inside (forces g member a (Finset.mem_filter.mp hit).1
            (Finset.mem_filter.mp hit).2)
        simp only [empty, Finset.card_empty, Nat.le_refl]
    _ = (G.filter fun g => g ∈ E).card * A.card := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ E.card * A.card := by
      apply Nat.mul_le_mul_right A.card
      apply Finset.card_le_card
      intro g member
      exact (Finset.mem_filter.mp member).2

theorem pairCount_le_pointwise (G A : Finset K)
    (x y : I → K) (den : I → Fin 4 → K) (R : I → Fin 4 → K[X])
    (event : Finset I → K → K → Prop) (S : Finset I)
    (capture : ∀ g ∈ G, ∀ a ∈ A, event S g a →
      ∀ i ∈ S, (fibreFold x y den R i g).eval a = 0) :
    pairCount G A event S ≤ pointwisePairCount G A x y den R S := by
  classical
  apply Finset.sum_le_sum
  intro g member
  apply Finset.card_le_card
  intro a hit
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hit).1,
    capture g member a (Finset.mem_filter.mp hit).1 (Finset.mem_filter.mp hit).2⟩

/-- Existing fixed-target bad-schedule bound, retaining legal pole rejection.
The proof uses one nonzero residual coordinate chosen from S before either
challenge; no new union over fibres or query indices appears. -/
theorem wrong_schedule_count (U C : Finset I) (G A : Finset K)
    (x y : I → K) (den : I → Fin 4 → K) (R : I → Fin 4 → K[X])
    (event : Finset I → K → K → Prop) (S : Finset I) (q d : Nat)
    (schedule : S ∈ U.powersetCard q) (wrong : ¬ S ⊆ C)
    (hd : d ≤ G.card) (ha : 3 ≤ A.card) (four : (4 : K) ≠ 0)
    (xy : ∀ i ∈ U, x i ≠ 0 ∧ y i ≠ 0)
    (degree : ∀ i ∈ U, ∀ j, (R i j).natDegree ≤ d)
    (common : ∀ i ∈ U, i ∈ C ↔ ∀ j, R i j = 0)
    (capture : ∀ g ∈ G, ∀ a ∈ A, event S g a →
      ∀ i ∈ S, (fibreFold x y den R i g).eval a = 0)
    (poles : ∀ g ∈ G, ∀ a ∈ A, event S g a →
      ∀ i ∈ S, ∀ j, den i j ≠ 0) :
    pairCount G A event S ≤ d*A.card + (G.card-d)*3 := by
  classical
  by_cases safe : ∀ i ∈ S, ∀ j, den i j ≠ 0
  · obtain ⟨i, member, outside⟩ := Finset.not_subset.mp wrong
    have inside := (Finset.mem_powersetCard.mp schedule).1 member
    have witness : ∃ j, R i j ≠ 0 := by
      by_contra missing
      apply outside
      apply (common i inside).mpr
      simpa only [not_exists, not_not] using missing
    obtain ⟨j, nonzero⟩ := witness
    exact (pairCount_le_pointwise G A x y den R event S capture).trans
      (pointwise_bad_schedule_count G A x y den R S i member j d hd ha
        nonzero (degree i inside j) four (xy i inside).1 (xy i inside).2 (safe i member j))
  · rw [pairCount_zero G A event S (fun g hg a ha accepted => safe (poles g hg a ha accepted))]
    exact Nat.zero_le _

/-- Distribution-sensitive improvement: an all-common schedule contributes
only on E, while an outside schedule uses the earlier joint gamma/fold bound.
The two parts are disjoint by schedule membership, not by conditioning the
remaining challenges on successful image or relation checks. -/
theorem fixed_tuple_count (U C : Finset I) (subset : C ⊆ U) (q : Nat)
    (G A E : Finset K) (x y : I → K) (den : I → Fin 4 → K)
    (R : I → Fin 4 → K[X]) (event : Finset I → K → K → Prop) (d : Nat)
    (hd : d ≤ G.card) (ha : 3 ≤ A.card) (four : (4 : K) ≠ 0)
    (xy : ∀ i ∈ U, x i ≠ 0 ∧ y i ≠ 0)
    (degree : ∀ i ∈ U, ∀ j, (R i j).natDegree ≤ d)
    (common : ∀ i ∈ U, i ∈ C ↔ ∀ j, R i j = 0)
    (capture : ∀ S ∈ U.powersetCard q, ∀ g ∈ G, ∀ a ∈ A, event S g a →
      ∀ i ∈ S, (fibreFold x y den R i g).eval a = 0)
    (poles : ∀ S ∈ U.powersetCard q, ∀ g ∈ G, ∀ a ∈ A, event S g a →
      ∀ i ∈ S, ∀ j, den i j ≠ 0)
    (charged : ∀ S ∈ U.powersetCard q, S ⊆ C →
      ∀ g ∈ G, ∀ a ∈ A, event S g a → g ∈ E) :
    totalCount U q G A event ≤
      C.card.choose q * (E.card*A.card) +
        (U.card.choose q-C.card.choose q) * (d*A.card + (G.card-d)*3) := by
  classical
  unfold totalCount
  rw [← Finset.sum_filter_add_sum_filter_not (U.powersetCard q) (fun S => S ⊆ C)]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _S ∈ (U.powersetCard q).filter (fun S => S ⊆ C), E.card*A.card := by
        apply Finset.sum_le_sum
        intro S member
        exact common_pair_count G A E event S
          (charged S (Finset.mem_filter.mp member).1 (Finset.mem_filter.mp member).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
        common_schedule_card U C subset q]
  · apply wrong_support_count U C subset q _ (pairCount G A event)
    intro S schedule wrong
    exact wrong_schedule_count U C G A x y den R event S q d schedule wrong hd ha four
      xy degree common (capture S schedule) (poles S schedule)

theorem common_fibre_cap (symbols fibres : Nat)
    (fourToOne : 4*fibres ≤ symbols) (insufficient : symbols < 38228) : fibres ≤ 9556 := by
  omega

/-- Exact normalization; the exception fraction multiplies the common-query
ratio. This statement does not itself establish the required ideal product law. -/
theorem normalized_count (total common g a e d : Nat)
    (hc : common ≤ total) (hd : d ≤ g)
    (ht : total ≠ 0) (hg : g ≠ 0) (ha : a ≠ 0) :
    (((common*(e*a)+(total-common)*(d*a+(g-d)*3) : Nat) : Rat)/(total*g*a)) =
      ((common : Rat)/total)*((e : Rat)/g) +
        (1-(common : Rat)/total)*
          ((d : Rat)/g+(1-(d : Rat)/g)*(3 : Rat)/a) := by
  have totalNonzero : (total : Rat) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have gammaNonzero : (g : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have alphaNonzero : (a : Rat) ≠ 0 := Nat.cast_ne_zero.mpr ha
  push_cast [Nat.cast_sub hc, Nat.cast_sub hd]
  field_simp

#print axioms pairCount_zero
#print axioms common_pair_count
#print axioms pairCount_le_pointwise
#print axioms wrong_schedule_count
#print axioms fixed_tuple_count
#print axioms common_fibre_cap
#print axioms normalized_count
end
end AspisV8.InsufficientOwnSupport
