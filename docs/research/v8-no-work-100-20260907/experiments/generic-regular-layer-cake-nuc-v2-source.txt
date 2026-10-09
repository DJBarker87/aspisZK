import TwoTailQueryBound
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Multiplicity-preserving finite regular layer cake

Source-review draft, not yet kernel-green. `active` and `support` are fixed tables
on factor occurrences and gamma; the alpha-dependent score remains under its
literal finite average. No independence, fixed pre-alpha final, disjoint
factors, or source sampler law is an input or conclusion.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.GenericRegularLayerCake
open Finset AspisV8.TwoTailQueryBound
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def aggregate {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (value : I → J → ℚ) : ℚ :=
  (factors.map (fun F => ∑ gamma ∈ Gamma, value F gamma)).sum

def tail {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (active : I → J → Prop) (support : I → J → Nat) (threshold : Nat) : Nat :=
  (factors.map (fun F => (Gamma.filter fun gamma =>
    active F gamma ∧ threshold ≤ support F gamma).card)).sum

/-- Index `t` runs L..U-1; the corresponding tail is H(t+1), not H(t). -/
def layer (weight : Nat → ℚ) (L U : Nat) (H : Nat → Nat) : ℚ :=
  weight L * H L + ∑ t ∈ Ico L U, (weight (t+1)-weight t) * H (t+1)

private theorem aggregate_congr {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (f g : I → J → ℚ) (equal : ∀ F ∈ factors, ∀ gamma ∈ Gamma, f F gamma = g F gamma) :
    aggregate factors Gamma f = aggregate factors Gamma g := by
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro F member
  exact Finset.sum_congr rfl (fun gamma inside => equal F member gamma inside)

private theorem aggregate_add {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (f g : I → J → ℚ) :
    aggregate factors Gamma (fun F gamma => f F gamma + g F gamma) =
      aggregate factors Gamma f + aggregate factors Gamma g := by
  induction factors using Multiset.induction_on with
  | empty => simp [aggregate]
  | @cons F factors ih =>
      simp only [aggregate, Multiset.map_cons, Multiset.sum_cons,
        Finset.sum_add_distrib] at ih ⊢
      linarith

private theorem aggregate_scale {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (c : ℚ) (f : I → J → ℚ) :
    aggregate factors Gamma (fun F gamma => c*f F gamma) = c*aggregate factors Gamma f := by
  induction factors using Multiset.induction_on with
  | empty => simp [aggregate]
  | @cons F factors ih =>
      simp only [aggregate, Multiset.map_cons, Multiset.sum_cons,
        ← Finset.mul_sum] at ih ⊢
      linarith

private theorem aggregate_sum {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (S : Finset Nat) (f : Nat → I → J → ℚ) :
    aggregate factors Gamma (fun F gamma => ∑ t ∈ S, f t F gamma) =
      ∑ t ∈ S, aggregate factors Gamma (f t) := by
  induction S using Finset.induction_on with
  | empty => simp [aggregate]
  | @insert t S absent ih =>
      simp only [Finset.sum_insert absent]
      rw [aggregate_add, ih]

private theorem aggregate_mono {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (f g : I → J → ℚ) (bound : ∀ F ∈ factors, ∀ gamma ∈ Gamma, f F gamma ≤ g F gamma) :
    aggregate factors Gamma f ≤ aggregate factors Gamma g := by
  apply Multiset.sum_map_le_sum_map
  intro F member
  exact Finset.sum_le_sum (fun gamma inside => bound F member gamma inside)

theorem aggregate_indicator {I J : Type*} (factors : Multiset I) (Gamma : Finset J)
    (active : I → J → Prop) (support : I → J → Nat) (threshold : Nat) :
    aggregate factors Gamma (fun F gamma =>
      if active F gamma ∧ threshold ≤ support F gamma then 1 else 0) =
      (tail factors Gamma active support threshold : ℚ) := by
  have one (F : I) : (∑ gamma ∈ Gamma,
      if active F gamma ∧ threshold ≤ support F gamma then (1 : ℚ) else 0) =
      ((Gamma.filter fun gamma => active F gamma ∧ threshold ≤ support F gamma).card : ℚ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  induction factors using Multiset.induction_on with
  | empty => simp [aggregate, tail]
  | @cons F factors ih =>
      simp only [aggregate, tail, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ih ⊢
      rw [one, ih]

private theorem one_layer (weight : Nat → ℚ) (L U m : Nat)
    (lower : L ≤ m) (upper : m ≤ U) :
    weight m = weight L + ∑ t ∈ Ico L U,
      (weight (t+1)-weight t)*(if t+1 ≤ m then 1 else 0) := by
  have filtered : (Ico L U).filter (fun t => t+1 ≤ m) = Ico L m := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have sumExact : (∑ t ∈ Ico L U,
      (weight (t+1)-weight t)*(if t+1 ≤ m then (1 : ℚ) else 0)) =
      ∑ t ∈ Ico L m, (weight (t+1)-weight t) := by
    calc
      _ = ∑ t ∈ Ico L U, if t+1 ≤ m then weight (t+1)-weight t else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      _ = _ := by rw [← Finset.sum_filter, filtered]
  rw [sumExact, Finset.sum_Ico_sub weight lower]
  ring

/-- Literal finite sum over factor occurrences and gamma witnesses. This is
an equality for the actual support table, not an assumed layer-cake premise. -/
theorem factor_gamma_layer_cake {I J : Type*}
    (factors : Multiset I) (Gamma : Finset J) (active : I → J → Prop)
    (support : I → J → Nat) (weight : Nat → ℚ) (L U : Nat)
    (bounds : ∀ F ∈ factors, ∀ gamma ∈ Gamma, active F gamma →
      L ≤ support F gamma ∧ support F gamma ≤ U) :
    aggregate factors Gamma (fun F gamma => if active F gamma then weight (support F gamma) else 0) =
      layer weight L U (tail factors Gamma active support) := by
  have point (F : I) (member : F ∈ factors) (gamma : J) (inside : gamma ∈ Gamma) :
      (if active F gamma then weight (support F gamma) else 0) =
        weight L*(if active F gamma ∧ L ≤ support F gamma then 1 else 0) +
        ∑ t ∈ Ico L U, (weight (t+1)-weight t)*
          (if active F gamma ∧ t+1 ≤ support F gamma then 1 else 0) := by
    by_cases present : active F gamma
    · obtain ⟨lower, upper⟩ := bounds F member gamma inside present
      simpa only [present, true_and, if_true, if_pos lower, mul_one] using
        one_layer weight L U (support F gamma) lower upper
    · simp only [present, false_and, if_false, mul_zero,
        Finset.sum_const_zero, add_zero]
  rw [aggregate_congr factors Gamma _ _ point]
  rw [aggregate_add, aggregate_scale, aggregate_indicator, aggregate_sum]
  simp only [aggregate_scale, aggregate_indicator, layer]

theorem layer_mono (weight : Nat → ℚ) (L U : Nat) (H B : Nat → Nat)
    (ordered : L ≤ U) (nonnegative : 0 ≤ weight L) (monotone : Monotone weight)
    (bound : ∀ m ∈ Icc L U, H m ≤ B m) :
    layer weight L U H ≤ layer weight L U B := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast bound L (by simp [ordered])) nonnegative
  · apply Finset.sum_le_sum
    intro t member
    have interval := Finset.mem_Ico.mp member
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast bound (t+1) (Finset.mem_Icc.mpr (by omega))
    · exact sub_nonneg.mpr (monotone (by omega))

def epsilon {AType : Type*} (A : Finset AType) : ℚ := min 1 ((3 : ℚ)/A.card)

private theorem epsilon_nonnegative {AType : Type*} (A : Finset AType) : 0 ≤ epsilon A := by
  apply le_min (by norm_num)
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- Direct factor-by-gamma-by-alpha consumer. `score` may depend arbitrarily
on alpha. The conditional bound is exactly the existing regular matching
moment interface, with zero contribution when no low prefix can exist.
Neither the active gamma sets nor the support table depends on alpha. -/
theorem factor_gamma_alpha_bound {I J AType : Type*}
    (factors : Multiset I) (Gamma : Finset J) (A : Finset AType)
    (active : I → J → Prop) (support : I → J → Nat)
    (score : I → J → AType → ℚ) (T q L U : Nat) (B : Nat → Nat)
    (ordered : L ≤ U)
    (bounds : ∀ F ∈ factors, ∀ gamma ∈ Gamma, active F gamma →
      L ≤ support F gamma ∧ support F gamma ≤ U)
    (tails : ∀ m ∈ Icc L U, tail factors Gamma active support m ≤ B m)
    (moment : ∀ F ∈ factors, ∀ gamma ∈ Gamma,
      mean A (score F gamma) ≤ if active F gamma then
        beta T q (support F gamma)+(1-beta T q (support F gamma))*epsilon A else 0) :
    aggregate factors Gamma (fun F gamma => mean A (score F gamma))/Gamma.card ≤
      (1-epsilon A)*layer (beta T q) L U B/Gamma.card +
        epsilon A*(tail factors Gamma active support L : ℚ)/Gamma.card := by
  have affine (F : I) (member : F ∈ factors) (gamma : J) (inside : gamma ∈ Gamma) :
      (if active F gamma then beta T q (support F gamma)+
        (1-beta T q (support F gamma))*epsilon A else 0) =
      (1-epsilon A)*(if active F gamma then beta T q (support F gamma) else 0) +
        epsilon A*(if active F gamma ∧ L ≤ support F gamma then 1 else 0) := by
    by_cases present : active F gamma
    · have lower := (bounds F member gamma inside present).1
      simp only [if_pos present, if_pos (And.intro present lower)]
      ring
    · simp only [present, false_and, if_false, mul_zero, add_zero]
  have summed := aggregate_mono factors Gamma _ _ moment
  rw [aggregate_congr factors Gamma _ _ affine, aggregate_add,
    aggregate_scale, aggregate_scale, aggregate_indicator,
    factor_gamma_layer_cake factors Gamma active support (beta T q) L U bounds] at summed
  have lc := layer_mono (beta T q) L U (tail factors Gamma active support) B ordered
    (beta_nonneg T q L) (fun _ _ h => beta_mono T q _ _ h) tails
  have nonnegative : 0 ≤ 1-epsilon A := sub_nonneg.mpr (min_le_left _ _)
  have total := summed.trans (add_le_add (mul_le_mul_of_nonneg_left lc nonnegative) (le_refl _))
  have divided := div_le_div_of_nonneg_right total (Nat.cast_nonneg Gamma.card)
  simpa only [add_div] using divided

/-- A single 3/k alpha charge follows from the SUM of factor incidences,
not merely the union cardinality. The full-alpha cardinal is explicit. -/
theorem alpha_charge {J AType : Type*} (Gamma : Finset J) (A : Finset AType)
    (nonempty : Gamma.Nonempty) (H k : Nat) (counts : H ≤ Gamma.card)
    (alphaCard : A.card = k) :
    epsilon A*(H : ℚ)/Gamma.card ≤ (3 : ℚ)/k := by
  have positive : (0 : ℚ) < Gamma.card := by exact_mod_cast nonempty.card_pos
  have ratio : (H : ℚ)/Gamma.card ≤ 1 :=
    (div_le_one positive).mpr (by exact_mod_cast counts)
  calc
    epsilon A*(H : ℚ)/Gamma.card = epsilon A*((H : ℚ)/Gamma.card) := by ring
    _ ≤ epsilon A*1 := mul_le_mul_of_nonneg_left ratio (epsilon_nonnegative A)
    _ = epsilon A := mul_one _
    _ ≤ (3 : ℚ)/k := by simpa only [epsilon, alphaCard] using min_le_right (1 : ℚ) ((3 : ℚ)/A.card)

/-- Same finite moment, normalized over the original Gamma, with the exact
cardinality comparison needed for the conservative alpha term retained. -/
theorem factor_gamma_alpha_conservative {I J AType : Type*}
    (factors : Multiset I) (Gamma : Finset J) (A : Finset AType)
    (active : I → J → Prop) (support : I → J → Nat)
    (score : I → J → AType → ℚ) (T q L U k : Nat) (B : Nat → Nat)
    (gammaNonempty : Gamma.Nonempty) (alphaNonempty : A.Nonempty)
    (alphaCard : A.card = k) (ordered : L ≤ U) (minimumCard : B L ≤ Gamma.card)
    (bounds : ∀ F ∈ factors, ∀ gamma ∈ Gamma, active F gamma →
      L ≤ support F gamma ∧ support F gamma ≤ U)
    (tails : ∀ m ∈ Icc L U, tail factors Gamma active support m ≤ B m)
    (moment : ∀ F ∈ factors, ∀ gamma ∈ Gamma,
      mean A (score F gamma) ≤ if active F gamma then
        beta T q (support F gamma)+(1-beta T q (support F gamma))*epsilon A else 0) :
    aggregate factors Gamma (fun F gamma => mean A (score F gamma))/Gamma.card ≤
      (1-epsilon A)*layer (beta T q) L U B/Gamma.card + (3 : ℚ)/k := by
  have bound := factor_gamma_alpha_bound factors Gamma A active support score T q L U B
    ordered bounds tails moment
  have count := (tails L (by simp [ordered])).trans minimumCard
  exact bound.trans (add_le_add (le_refl _) (alpha_charge Gamma A gammaNonempty
    (tail factors Gamma active support L) k count alphaCard))

theorem beta_increment (T q t : Nat) (positive : 0 < q) :
    beta T q (t+1)-beta T q t = ((t.choose (q-1) : Nat) : ℚ)/T.choose q := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  unfold beta
  rw [Nat.choose_succ_succ, Nat.cast_add]
  simp only [Nat.succ_sub_one]
  ring

theorem selected_minimum_floor :
    (1048576*239599331)/(4*9558-1026) = 6752623450 := by norm_num

#print axioms aggregate_indicator
#print axioms factor_gamma_layer_cake
#print axioms layer_mono
#print axioms factor_gamma_alpha_bound
#print axioms alpha_charge
#print axioms factor_gamma_alpha_conservative
#print axioms beta_increment
#print axioms selected_minimum_floor

end
end AspisV8.GenericRegularLayerCake
