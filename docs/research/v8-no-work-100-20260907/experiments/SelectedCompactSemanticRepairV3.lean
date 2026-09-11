import JointImageGame
import AspisFormal.V6AcceptedPathObligations

/-! Exact compact semantic recurrence and its authentication/repair split.
Only the pinned V6 semantic grammar is imported: 27 sent coefficients per
round, with coefficient one reconstructed from the incoming claim. No old
448-byte full-message framing or old 25-lane helper bound is used.

The boundary and repair proofs are narrow source ports of
Pool.V7CompactSemanticBinding and V5AcceptedSumcheckSourceBridge. A reference
trace remains explicit; it is not authenticated merely by being a record.
Probability additionally needs both messages fixed before the current
challenge, and a separately supplied fresh-law/source connection.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedCompactSemanticRepair
open scoped BigOperators
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability AspisV8.JointImageGame
open AspisV6TranscriptRelationGrammar AspisV6AcceptedPathObligations
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

def partsPolynomial (incoming : K) (parts : SemanticRoundParts K) : K[X] :=
  monomialPolynomial (semanticCoefficient incoming parts)

theorem parts_eval (incoming : K) (parts : SemanticRoundParts K) (x : K) :
    (partsPolynomial incoming parts).eval x=semanticEvaluate incoming parts x := by
  simp [partsPolynomial, monomialPolynomial, semanticEvaluate, Polynomial.eval_finsetSum]

theorem coefficient_sum (incoming : K) (parts : SemanticRoundParts K) :
    (∑ coefficient : Fin 28, semanticCoefficient incoming parts coefficient) =
      parts.constant+reconstructedSemanticLinear incoming parts+∑ i, parts.higher i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have higher (i : Fin 26) :
      semanticCoefficient incoming parts i.succ.succ=parts.higher i := by
    simp [semanticCoefficient]
  simp_rw [higher]
  simp [semanticCoefficient, add_assoc]

theorem parts_boundary (incoming : K) (parts : SemanticRoundParts K) :
    (partsPolynomial incoming parts).eval 0+
      (partsPolynomial incoming parts).eval 1=incoming := by
  have atZero : (partsPolynomial incoming parts).eval 0=parts.constant := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    change (monomialPolynomial (semanticCoefficient incoming parts)).coeff 0=parts.constant
    simpa [semanticCoefficient] using
      monomialPolynomial_coeff (semanticCoefficient incoming parts) (0 : Fin 28)
  have atOne : (partsPolynomial incoming parts).eval 1=
      ∑ i : Fin 28, semanticCoefficient incoming parts i := by
    simp [partsPolynomial, monomialPolynomial, Polynomial.eval_finsetSum]
  rw [atZero, atOne, coefficient_sum]
  simpa only [semanticBoundaryFromParts, add_assoc] using
    reconstructed_semantic_linear_has_exact_boundary incoming parts

def compactPolynomial (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) : K[X] :=
  partsPolynomial (semanticRunningClaim fields point round.val) (semanticParts fields round)

theorem partsPolynomial_degree (incoming : K) (parts : SemanticRoundParts K) :
    (partsPolynomial incoming parts).natDegree ≤ 27 :=
  monomialPolynomial_natDegree_le (by decide : 0 < 28) _

theorem compact_degree (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) : (compactPolynomial fields point round).natDegree ≤ 27 := by
  simpa only [compactPolynomial] using partsPolynomial_degree
    (semanticRunningClaim fields point round.val) (semanticParts fields round)

theorem compact_boundary (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    (compactPolynomial fields point round).eval 0+
      (compactPolynomial fields point round).eval 1 =
        semanticRunningClaim fields point round.val :=
  parts_boundary _ _

theorem compact_successor (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    (compactPolynomial fields point round).eval (point round)=
      semanticRunningClaim fields point (round.val+1) := by
  unfold compactPolynomial
  rw [parts_eval, semanticRunningClaim]
  simp only [round.isLt, dif_pos]

def referenceClaim (initial : K) (messages : Fin 10 → K[X]) (point : Fin 10 → K) :
    Fin 11 → K := Fin.cases initial (fun round => (messages round).eval (point round))

/-- A fixed-oracle reference restriction sequence. The later causal adapter
must establish its prefix dependence, not choose it after each challenge. -/
structure ReferenceTrace (table : Fin 1024 → K) (point : Fin 10 → K) where
  messages : Fin 10 → K[X]
  degree : ∀ round, (messages round).natDegree ≤ 27
  boundary : ∀ round, (messages round).eval 0+(messages round).eval 1 =
    referenceClaim (∑ row, table row) messages point round.castSucc

def difference (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) (step : Fin 11) : K :=
  semanticRunningClaim fields point step.val -
    referenceClaim (∑ row, table row) reference.messages point step

theorem running_initial (fields : FixedFieldView K) (point : Fin 10 → K) :
    semanticRunningClaim fields point 0=fields.initialClaim := rfl

theorem reference_initial (initial : K) (messages : Fin 10 → K[X]) (point : Fin 10 → K) :
    referenceClaim initial messages point 0=initial := rfl

theorem difference_initial (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) :
    difference fields point reference 0=fields.initialClaim-(∑ row, table row) := by
  unfold difference
  rw [running_initial, reference_initial]

theorem difference_terminal (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) :
    difference fields point reference (Fin.last 10)=semanticTerminalClaim fields point-
      referenceClaim (∑ row, table row) reference.messages point (Fin.last 10) := rfl

def Repair (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) (round : Fin 10) : Prop :=
  difference fields point reference round.castSucc≠0 ∧
    difference fields point reference round.succ=0

/-- Symbolic ten-step propagation; no concrete recurrence is reduced. -/
theorem ten_step_repair (d : Fin 11 → K) (initial : d 0≠0)
    (terminal : d (Fin.last 10)=0) :
    ∃ round : Fin 10, d round.castSucc≠0 ∧ d round.succ=0 := by
  by_contra noRepair
  have propagate : ∀ round : Fin 10, d round.castSucc≠0 → d round.succ≠0 := by
    intro round before after
    exact noRepair ⟨round, before, after⟩
  have all : ∀ step : Fin 11, d step≠0 := Fin.induction initial propagate
  exact all (Fin.last 10) terminal

theorem repair_polynomial (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point)
    (round : Fin 10) (repair : Repair fields point reference round) :
    compactPolynomial fields point round-reference.messages round≠0 ∧
    (compactPolynomial fields point round-reference.messages round).natDegree ≤ 27 ∧
    (compactPolynomial fields point round-reference.messages round).eval (point round)=0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro zero
    have same : compactPolynomial fields point round=reference.messages round := sub_eq_zero.mp zero
    have sameBoundary := congrArg (fun p : K[X] => p.eval 0+p.eval 1) same
    rw [compact_boundary, reference.boundary] at sameBoundary
    apply repair.1
    exact sub_eq_zero.mpr sameBoundary
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (compact_degree fields point round) (reference.degree round))
  · have after := repair.2
    change semanticRunningClaim fields point (round.val+1)-
      (reference.messages round).eval (point round)=0 at after
    rw [← compact_successor fields point round] at after
    simpa only [Polynomial.eval_sub] using after

def badRound (S : Finset K) (claimed reference : K[X]) : Finset K :=
  if claimed-reference=0 then ∅ else S.filter fun x => (claimed-reference).eval x=0

theorem badRound_card (S : Finset K) (claimed reference : K[X])
    (claimedDegree : claimed.natDegree ≤ 27) (referenceDegree : reference.natDegree ≤ 27) :
    (badRound S claimed reference).card ≤ 27 := by
  classical
  by_cases zero : claimed-reference=0
  · simp [badRound, zero]
  · rw [badRound, if_neg zero]
    exact root_count S _ zero 27 ((Polynomial.natDegree_sub_le _ _).trans
      (max_le claimedDegree referenceDegree))

theorem mem_badRound_of_root (S : Finset K) (claimed reference : K[X]) (x : K)
    (inside : x∈S) (nonzero : claimed-reference≠0)
    (zero : (claimed-reference).eval x=0) : x∈badRound S claimed reference := by
  classical
  rw [badRound, if_neg nonzero]
  exact Finset.mem_filter.mpr ⟨inside, zero⟩

theorem repair_hits_badRound (S : Finset K) (fields : FixedFieldView K)
    (point : Fin 10 → K) {table : Fin 1024 → K} (reference : ReferenceTrace table point)
    (round : Fin 10) (inside : point round∈S) (repair : Repair fields point reference round) :
    point round∈badRound S (compactPolynomial fields point round) (reference.messages round) := by
  classical
  have details := repair_polynomial fields point reference round repair
  have nonzero := details.1
  have root := details.2.2
  rw [badRound, if_neg nonzero]
  exact Finset.mem_filter.mpr ⟨inside, root⟩

def maskedTable (eta : K) (real mask : Fin 1024 → K) : Fin 1024 → K :=
  fun row => mask row+eta*real row

theorem masked_sum (eta : K) (real mask : Fin 1024 → K) :
    (∑ row, maskedTable eta real mask row)=(∑ row, mask row)+eta*∑ row, real row := by
  simp only [maskedTable, Finset.sum_add_distrib, Finset.mul_sum]

/-- Total deterministic split for the literal compact recurrence. Initial
mask authentication and terminal reference authentication remain failures,
not consequences of a scalar terminal check. Eta is the same supplied
nonzero verifier challenge throughout. -/
theorem compact_unmasked_or_failures (fields : FixedFieldView K) (point : Fin 10 → K)
    (eta : K) (etaNonzero : eta≠0) (real mask : Fin 1024 → K)
    (reference : ReferenceTrace (maskedTable eta real mask) point) :
    (∑ row, real row)=0 ∨
    fields.initialClaim≠(∑ row, mask row) ∨
    semanticTerminalClaim fields point≠
      referenceClaim (∑ row, maskedTable eta real mask row) reference.messages point (Fin.last 10) ∨
    ∃ round, Repair fields point reference round := by
  classical
  by_cases maskFailure : fields.initialClaim≠(∑ row, mask row)
  · exact Or.inr (Or.inl maskFailure)
  by_cases terminalFailure : semanticTerminalClaim fields point≠
      referenceClaim (∑ row, maskedTable eta real mask row) reference.messages point (Fin.last 10)
  · exact Or.inr (Or.inr (Or.inl terminalFailure))
  by_cases wrong : fields.initialClaim≠(∑ row, maskedTable eta real mask row)
  · right; right; right
    apply ten_step_repair (difference fields point reference)
    · rw [difference_initial]
      exact sub_ne_zero.mpr wrong
    · rw [difference_terminal]
      exact sub_eq_zero.mpr (not_ne_iff.mp terminalFailure)
  · left
    have boundary : (∑ row, maskedTable eta real mask row)=(∑ row, mask row) :=
      (not_ne_iff.mp wrong).symm.trans (not_ne_iff.mp maskFailure)
    rw [masked_sum] at boundary
    have productZero : eta*(∑ row, real row)=0 := by
      exact add_left_cancel (boundary.trans (add_zero _).symm)
    exact (mul_eq_zero.mp productZero).resolve_left etaNonzero

#print axioms parts_boundary
#print axioms compact_degree
#print axioms compact_successor
#print axioms ten_step_repair
#print axioms repair_polynomial
#print axioms badRound_card
#print axioms repair_hits_badRound
#print axioms compact_unmasked_or_failures
end
end AspisV8.SelectedCompactSemanticRepair


