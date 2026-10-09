import R0P.SemMaxErr
import R0P.MaskD2
import R0P.MaskFiatShamir

/-! Exact accounting for the authorized eta coefficient 100 and the
32-round masked Fiat–Shamir bound. The final q22 row is the maximum. -/
set_option autoImplicit false
namespace R0P.Mask
open FS R0P.SemSource R0P.SemMaxErr R0C.SlackStatement AspisWideTower
noncomputable section

/-- Insert one eta budget, shifting the already degree-27 alpha rows and
all later rows. This is an accounting family, not a claim of masked D2. -/
def combinedD2BudgetWithEta (etaBudget : ℚ) (i : Nat) : ℚ :=
  if i < 14 then combinedD2Budget i
  else if i = 14 then etaBudget
  else combinedD2Budget (i - 1)

/-- The final query row is unchanged by insertion of eta. -/
theorem combinedD2BudgetWithEta_last (etaBudget : ℚ) :
    combinedD2BudgetWithEta etaBudget 31 = epsilonSlack WideExact delta0 4 := by
  simp only [combinedD2BudgetWithEta, if_neg (show ¬ (31 : Nat) < 14 by omega),
    if_neg (show ¬ (31 : Nat) = 14 by omega), Nat.reduceSub,
    combinedD2Budget, dif_neg (show ¬ (30 : Nat) < 24 by omega),
    if_neg (show ¬ (30 : Nat) < 26 by omega),
    if_neg (show ¬ (30 : Nat) < 30 by omega)]

/-- Any inserted eta budget below the query row preserves the exact maximum. -/
theorem combined_maxErrWithEta (etaBudget : ℚ)
    (hEta : etaBudget ≤ epsilonSlack WideExact delta0 4) :
    maxErr (combinedD2BudgetWithEta etaBudget) 32 = epsilonSlack WideExact delta0 4 := by
  rw [← combinedD2BudgetWithEta_last etaBudget]
  apply maxErr_eq_of_le _ _ 31 (by omega)
  · rw [combinedD2BudgetWithEta_last]
    exact query_nonneg
  · intro i _
    rw [combinedD2BudgetWithEta_last]
    unfold combinedD2BudgetWithEta
    split_ifs
    · exact combined_row_le_query i
    · exact hEta
    · exact combined_row_le_query (i - 1)

/-- The authorized coefficient 100 falls within this proved range. -/
theorem combined_maxErrWithEta_coefficient (c : ℚ) (hc0 : 0 ≤ c) (hc : c ≤ 217600) :
    maxErr (combinedD2BudgetWithEta ((1 + deltaQ) * c /
      (AspisCircleGroupOrder.P : ℚ)^4)) 32 = epsilonSlack WideExact delta0 4 :=
  combined_maxErrWithEta _ (small_budget_le_query c hc0 hc)

/-- The two circle rows use the larger authorized 2/P^4 envelope. -/
theorem masked_circle_le_query :
    2 / (AspisCircleGroupOrder.P : ℚ)^4 ≤ epsilonSlack WideExact delta0 4 := by
  apply le_trans _ (small_budget_le_query 2 (by norm_num) (by norm_num))
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
  have hδ := deltaQ_nonneg
  linarith

theorem combined_rowZ_le_query (i : Nat) :
    combinedD2BudgetZ i ≤ epsilonSlack WideExact delta0 4 := by
  unfold combinedD2BudgetZ
  split_ifs with h14 heq h25 h27 h31
  · exact combined_row_le_query i
  · have h := small_budget_le_query 100 (by norm_num) (by norm_num)
    convert h using 1
    ring
  · simpa only [mul_div_assoc] using small_budget_le_query 2700 (by norm_num) (by norm_num)
  · exact masked_circle_le_query
  · exact opening_le_query (i - 27) (by omega)
  · exact le_rfl

/-- The final q22 row attains the maximum for the fixed masked budget. -/
theorem combined_maxErrZ :
    maxErr combinedD2BudgetZ 32 = epsilonSlack WideExact delta0 4 := by
  have hlast : combinedD2BudgetZ 31 = epsilonSlack WideExact delta0 4 := by
    simp only [combinedD2BudgetZ, if_neg (show ¬ (31 : Nat) < 14 by omega),
      if_neg (show ¬ (31 : Nat) = 14 by omega),
      if_neg (show ¬ (31 : Nat) < 25 by omega),
      if_neg (show ¬ (31 : Nat) < 27 by omega),
      if_neg (show ¬ (31 : Nat) < 31 by omega)]
  rw [← hlast]
  apply maxErr_eq_of_le _ _ 31 (by omega)
  · rw [hlast]; exact query_nonneg
  · intro i _
    rw [hlast]
    exact combined_rowZ_le_query i

#print axioms masked_circle_le_query
#print axioms combined_rowZ_le_query
#print axioms combined_maxErrZ

#print axioms combinedD2BudgetWithEta_last
#print axioms combined_maxErrWithEta
#print axioms combined_maxErrWithEta_coefficient
end
end R0P.Mask

namespace R0P.Mask
open R0C.SlackStatement
open FS FS2 FS2.Duplex R0C.V3 R0P.SemSource R0P.SemD3Glue R0P.MaskDuplex AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
variable (maskClaims : (Fin 29 → WideExact) → (Fin 10 → WideExact) → WideExact) (hMask : MaskDegree maskClaims)
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
variable (msg : Pf → Nat → MsgZ WideExact)
local notation "prZ" => combinedProtocolZ B p msg (fun _ _ => none)
local notation "VZ" => FS2.verifier (prZ) (combinedDecisionZ maskClaims B)

include hMask in
/-- Exact q22 closed form of the masked theorem43 instance. -/
theorem combined_fiat_shamirZ_closed (x : TypedContext WideExact Sfield) (hr32 : p.rounds = 32)
    (hσsem : ∀ (i : Nat) (_hi : i < 25) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 26 s = R0C.SemStatement.Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (27+j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VZ) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (FS2.accepts (eval H (FS2.experiment P (VZ) x)) ∧
        FS2.extractFails (prZ) x (eval H (FS2.experiment P (VZ) x)))) ≤
      (Qtot : ℚ) * ((1 + delta0) *
        ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))) + κ Qtot := by
  have h := combined_fiat_shamirZ maskClaims hMask B p msg x hr32 hσsem hσz0 hσz1 hσopen P Qtot hQ
  rw [combined_maxErrZ] at h
  exact h

#print axioms combined_fiat_shamirZ_closed
end
end R0P.Mask
