import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic

/-! Compose the two actual off-family agreement tails with fresh query
probabilities. No union over candidate families and no positive work credit.
The two tail-cardinality inputs are discharged by separate selected-code
theorems, not supplied as an unexplained small probability in the endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.TwoTailQueryBound
open Finset
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Definitionally the existing game's finite average; isolated here so the
generic counting leaf need not load any concrete code or causal-game module. -/
def mean {J : Type*} (S : Finset J) (f : J → ℚ) : ℚ :=
  (∑ j∈S, f j)/S.card

theorem mean_mono {J : Type*} (S : Finset J) (f g : J → ℚ)
    (h : ∀ j∈S, f j≤g j) : mean S f≤mean S g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

theorem mean_add {J : Type*} (S : Finset J) (f g : J → ℚ) :
    mean S (fun j => f j+g j)=mean S f+mean S g := by
  simp only [mean,Finset.sum_add_distrib,add_div]

theorem mean_constant {J : Type*} (S : Finset J) (nonempty : S.Nonempty) (c : ℚ) :
    mean S (fun _ => c)=c := by
  have card : (S.card:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt nonempty.card_pos
  simp only [mean,Finset.sum_const,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c card

def beta (T q m : Nat) : ℚ := (m.choose q : ℚ)/T.choose q

theorem beta_nonneg (T q m : Nat) : 0≤beta T q m := by
  unfold beta
  positivity

theorem beta_mono (T q m n : Nat) (ordered : m≤n) : beta T q m≤beta T q n := by
  unfold beta
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose q ordered)
    (Nat.cast_nonneg _)

theorem beta_unit (T q m : Nat) (count : q≤T) (bounded : m≤T) : beta T q m≤1 := by
  have positive : (T.choose q : ℚ)≠0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos count)
  have bound := beta_mono T q m T bounded
  simpa only [beta,div_self positive] using bound

theorem average_indicator {J : Type*} (S : Finset J) (event : J → Prop)
    [DecidablePred event] (c : ℚ) :
    mean S (fun j => if event j then c else 0)=
      ((S.filter event).card : ℚ)/S.card*c := by
  classical
  unfold mean
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

/-- Actual low/middle/high matching classes, not a family-wise query union.
`M` and `outside` are fixed before the fresh schedule at each challenge. -/
theorem two_tail_bound {J : Type*} (S : Finset J) (nonempty : S.Nonempty)
    (M : J → Nat) (outside : J → Prop) (T q a t C H : Nat)
    (positive : 0<a) (ordered : a≤t) (queries : q≤T)
    (bounded : ∀ j∈S, M j≤T)
    (lowTail : (S.filter fun j => outside j ∧ a≤M j).card≤C)
    (highTail : (S.filter fun j => outside j ∧ t≤M j).card≤H) :
    mean S (fun j => if outside j then beta T q (M j) else 0)≤
      beta T q (a-1)+(C:ℚ)/S.card*beta T q (t-1)+(H:ℚ)/S.card := by
  classical
  let low := fun j => outside j ∧ a≤M j
  let high := fun j => outside j ∧ t≤M j
  have point (j : J) (member : j∈S) :
      (if outside j then beta T q (M j) else 0)≤
        (beta T q (a-1)+(if low j then beta T q (t-1) else 0))+
          (if high j then (1:ℚ) else 0) := by
    by_cases out : outside j
    · by_cases upper : t≤M j
      · have lo : low j := ⟨out,ordered.trans upper⟩
        have hi : high j := ⟨out,upper⟩
        simp only [if_pos out,if_pos lo,if_pos hi]
        have unit := beta_unit T q (M j) queries (bounded j member)
        linarith [beta_nonneg T q (a-1),beta_nonneg T q (t-1)]
      · have hi : ¬high j := fun h => upper h.2
        by_cases lower : a≤M j
        · have lo : low j := ⟨out,lower⟩
          simp only [if_pos out,if_pos lo,if_neg hi,add_zero]
          have small := beta_mono T q (M j) (t-1) (by omega)
          linarith [beta_nonneg T q (a-1)]
        · have lo : ¬low j := fun h => lower h.2
          simp only [if_pos out,if_neg lo,if_neg hi,add_zero]
          exact beta_mono T q (M j) (a-1) (by omega)
    · have lo : ¬low j := fun h => out h.1
      have hi : ¬high j := fun h => out h.1
      simp only [if_neg out,if_neg lo,if_neg hi,add_zero]
      exact beta_nonneg T q (a-1)
  have summed := mean_mono S _ _ point
  rw [mean_add,mean_add,mean_constant S nonempty] at summed
  rw [average_indicator S low (beta T q (t-1)),
    average_indicator S high 1,mul_one] at summed
  have lo : ((S.filter low).card : ℚ)≤C := by exact_mod_cast lowTail
  have hi : ((S.filter high).card : ℚ)≤H := by exact_mod_cast highTail
  have dlo := div_le_div_of_nonneg_right lo (Nat.cast_nonneg S.card)
  have dhi := div_le_div_of_nonneg_right hi (Nat.cast_nonneg S.card)
  have weighted := mul_le_mul_of_nonneg_right dlo (beta_nonneg T q (t-1))
  exact summed.trans (by linarith)

#print axioms mean_mono
#print axioms mean_add
#print axioms mean_constant
#print axioms beta_nonneg
#print axioms beta_mono
#print axioms beta_unit
#print axioms average_indicator
#print axioms two_tail_bound
end
end AspisV8.TwoTailQueryBound
