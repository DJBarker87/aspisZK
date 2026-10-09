import R0P.SemFiatShamir
import R0C.SlackBits

/-! Exact accounting for the combined 31-round error schedule. The query
row dominates every semantic, circle, and opening-field row. -/
set_option autoImplicit false
namespace R0P.SemMaxErr
open FS R0P.SemSource R0C.SlackStatement AspisWideTower
noncomputable section

/-- Bound the fold including its zero seed, before using a concrete field. -/
theorem maxErr_le_of_le (e : Nat → ℚ) (r : Nat) (a : ℚ)
    (hn : 0 ≤ a) (hb : ∀ i, i < r → e i ≤ a) : maxErr e r ≤ a := by
  have hfold (l : List Nat) (h : ∀ i ∈ l, e i ≤ a) :
      l.foldr (fun i m => max (e i) m) 0 ≤ a := by
    induction l with
    | nil => exact hn
    | cons i l ih =>
        exact max_le (h i (by simp))
          (ih (fun j hj => h j (by simp only [List.mem_cons]; exact Or.inr hj)))
  exact hfold (List.range r) (fun i hi => hb i (List.mem_range.mp hi))

/-- An attained upper bound is the maximum when it also bounds the zero seed. -/
theorem maxErr_eq_of_le (e : Nat → ℚ) (r j : Nat) (hj : j < r)
    (hn : 0 ≤ e j) (hb : ∀ i, i < r → e i ≤ e j) : maxErr e r = e j := by
  exact le_antisymm (maxErr_le_of_le e r (e j) hn hb) (FS.le_maxErr e r j hj)

#print axioms maxErr_le_of_le
#print axioms maxErr_eq_of_le

/-- The largest semantic coefficient follows from the symbolic budget branches. -/
theorem semRoundBudget_le (i : Fin 24) : semRoundBudget i ≤ 2176 := by
  unfold semRoundBudget
  split_ifs <;> omega

/-- Use the two checked 22-factor counts; never reduce a Pascal recurrence. -/
theorem semantic_numeric_bound :
    (2 * 217600 : ℚ) / (AspisCircleGroupOrder.P : ℚ)^4 ≤
      (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  norm_num [R0C.SlackBits.bad_query_count, R0C.SlackObstruction.query_count,
    AspisCircleGroupOrder.P]

theorem query_nonneg : 0 ≤ epsilonSlack WideExact delta0 4 := by
  change 0 ≤ (1 + delta0) *
    ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))
  exact mul_nonneg (add_nonneg zero_le_one R0C.ConcreteSlack.delta0_nonneg)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- A common rational bound covers both semantic rows and circle rows. -/
theorem small_budget_le_query (b : ℚ) (hb0 : 0 ≤ b) (hb : b ≤ 217600) :
    (1 + deltaQ) * b / (AspisCircleGroupOrder.P : ℚ)^4 ≤
      epsilonSlack WideExact delta0 4 := by
  have hδ : 1 + deltaQ ≤ 2 := by
    have h : deltaQ ≤ 1 := deltaQ_small.trans (by norm_num)
    linarith
  calc
    (1 + deltaQ) * b / (AspisCircleGroupOrder.P : ℚ)^4 ≤
        (2 * 217600 : ℚ) / (AspisCircleGroupOrder.P : ℚ)^4 :=
      div_le_div_of_nonneg_right (mul_le_mul hδ hb hb0 (by norm_num))
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) :=
      semantic_numeric_bound
    _ ≤ epsilonSlack WideExact delta0 4 := by
      change _ ≤ (1 + delta0) *
        ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))
      have hs : (1 : ℚ) ≤ 1 + delta0 := le_add_of_nonneg_right
        R0C.ConcreteSlack.delta0_nonneg
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
        (div_nonneg (Nat.cast_nonneg (Nat.choose 9557 22))
          (Nat.cast_nonneg (Nat.choose 262144 22)))

theorem semantic_le_query (i : Fin 24) :
    (1 + deltaQ) * ((100 * semRoundBudget i : Nat) /
      (AspisCircleGroupOrder.P ^ 4 : ℚ)) ≤ epsilonSlack WideExact delta0 4 := by
  rw [← mul_div_assoc]
  apply small_budget_le_query _ (Nat.cast_nonneg _)
  exact_mod_cast (show 100 * semRoundBudget i ≤ 217600 by
    have h := semRoundBudget_le i
    omega)

theorem circle_le_query :
    (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 ≤
      epsilonSlack WideExact delta0 4 := by
  simpa only [mul_one] using small_budget_le_query 1 (by norm_num) (by norm_num)

theorem opening_le_query (i : Nat) (hi : i < 5) :
    epsilonSlack WideExact delta0 i ≤ epsilonSlack WideExact delta0 4 :=
  mul_le_mul_of_nonneg_left (R0C.SlackBits.row_le_query i hi)
    (add_nonneg zero_le_one R0C.ConcreteSlack.delta0_nonneg)

#print axioms semRoundBudget_le
#print axioms semantic_numeric_bound
#print axioms query_nonneg
#print axioms small_budget_le_query
#print axioms semantic_le_query
#print axioms circle_le_query
#print axioms opening_le_query

theorem combined_row_le_query (i : Nat) :
    combinedD2Budget i ≤ epsilonSlack WideExact delta0 4 := by
  unfold combinedD2Budget
  split_ifs with h24 h26 h30
  · exact semantic_le_query ⟨i, h24⟩
  · exact circle_le_query
  · exact opening_le_query (i - 26) (by omega)
  · exact le_rfl

/-- Row 30 attains the maximum over all 31 challenge rounds. -/
theorem combined_maxErr :
    maxErr combinedD2Budget 31 = epsilonSlack WideExact delta0 4 := by
  have h30 : combinedD2Budget 30 = epsilonSlack WideExact delta0 4 := by
    simp only [combinedD2Budget, dif_neg (show ¬ (30 : Nat) < 24 by omega),
      if_neg (show ¬ (30 : Nat) < 26 by omega),
      if_neg (show ¬ (30 : Nat) < 30 by omega)]
  rw [← h30]
  apply maxErr_eq_of_le _ _ 30 (by omega)
  · rw [h30]
    exact query_nonneg
  · intro i _
    rw [h30]
    exact combined_row_le_query i

#print axioms combined_row_le_query
#print axioms combined_maxErr
end
end R0P.SemMaxErr

namespace R0P.SemDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P.SemSource R0P.SemD3Glue
open R0C.SlackStatement R0P.SemMaxErr
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params CM (R0C.SemStatement.Chal SemE SemE) L)
variable (msg : Pf → Nat → CM)

local notation "prC" => combinedProtocol B p msg (fun _ _ => none)
local notation "VC" => FS2.verifier (prC) (combinedDecision B)

/-- The theorem43 instance with its exact combined error budget substituted. -/
theorem combined_fiat_shamir_closed (x : CX Sfield) (hr31 : p.rounds = 31)
    (hσsem : ∀ (i : Nat) (_hi : i < 24) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 24 s = R0C.SemStatement.Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (26 + j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VC) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (VC) x)) ∧
          FS2.extractFails (prC) x (eval H (FS2.experiment P (VC) x)))) ≤
      (Qtot : ℚ) * ((1 + delta0) *
        ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))) + κ Qtot := by
  have h := combined_fiat_shamir B p msg x hr31 hσsem hσz0 hσz1 hσopen P Qtot hQ
  rw [combined_maxErr] at h
  exact h

#print axioms combined_fiat_shamir_closed
end
end R0P.SemDuplex
