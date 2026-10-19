import RRInitialMessageRecovery
import RRFinalMessageRecovery
import Mathlib.Algebra.CharP.Algebra

set_option autoImplicit false
noncomputable section
namespace AspisR1.RRMessageRecoveryLaw
open CompPoly Polynomial RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts AspisR1.RRConcreteTraversal
open AspisR1.RRConcreteRawRecovery AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling AspisV8PairedCommitment

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

theorem field_odd : ringChar K ≠ 2 := by
  letI : CharP K AspisCircleGroupOrder.P :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod AspisCircleGroupOrder.P) K)
      AspisCircleGroupOrder.P (by norm_num [AspisCircleGroupOrder.P])
  rw [ringChar.eq K AspisCircleGroupOrder.P]
  norm_num [AspisCircleGroupOrder.P]

def initialAbortMass (q t : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ 112)
    (hn : model s ≠ 0) : ℚ :=
  mean (fun H : {i : Nat // i ∈ Finset.range
      (1025 * mass 112 (initialValidState 112 s hd hn))} → Fin t → K × K =>
    abortIndicator (AspisR1.RRInitialMessageRecovery.recoverMessages 112 q t s hd hn H))

def finalAbortMass (q t : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ 112)
    (hn : model s ≠ 0) : ℚ :=
  mean (fun H : {i : Nat // i ∈ Finset.range
      (256 * mass 112 (initialValidState 112 s hd hn))} → Fin t → K × K =>
    abortIndicator (AspisR1.RRFinalMessageRecovery.recoverMessages 112 q t s hd hn H))

theorem initialAbortMass_le (q t : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ 112)
    (hn : model s ≠ 0) (hq : q = Fintype.card K) :
    initialAbortMass q t s hd hn ≤ (1025 : ℚ) * 112 * (1/2)^t := by
  unfold initialAbortMass
  rw [mean_congr (fun H =>
    AspisR1.RRInitialMessageRecovery.recoverMessages_abort_indicator 112 q t s hd hn H)]
  exact recover_abort_le 112 q t 1025 s hd hn hq field_odd

theorem finalAbortMass_le (q t : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ 112)
    (hn : model s ≠ 0) (hq : q = Fintype.card K) :
    finalAbortMass q t s hd hn ≤ (256 : ℚ) * 112 * (1/2)^t := by
  unfold finalAbortMass
  rw [mean_congr (fun H =>
    AspisR1.RRFinalMessageRecovery.recoverMessages_abort_indicator 112 q t s hd hn H)]
  exact recover_abort_le 112 q t 256 s hd hn hq field_odd

/-- Sum of the two actual message-recovery masses, not yet a joint adaptive
caller theorem. The bit-tape conversion is also a separate obligation. -/
theorem two_message_recovery_masses_lt (q : Nat) (s0 s1 : RawState K)
    (hd0 : ∀ i ≤ s0.maxX, (inputPolynomial s0.rows i).natDegree ≤ 112)
    (hn0 : model s0 ≠ 0)
    (hd1 : ∀ i ≤ s1.maxX, (inputPolynomial s1.rows i).natDegree ≤ 112)
    (hn1 : model s1 ≠ 0) (hq : q = Fintype.card K) :
    initialAbortMass q 149 s0 hd0 hn0 + finalAbortMass q 149 s1 hd1 hn1 <
      (1 : ℚ) / 2^131 := by
  apply lt_of_le_of_lt (add_le_add
    (initialAbortMass_le q 149 s0 hd0 hn0 hq)
    (finalAbortMass_le q 149 s1 hd1 hn1 hq))
  norm_num

#print axioms field_odd
#print axioms initialAbortMass_le
#print axioms finalAbortMass_le
#print axioms two_message_recovery_masses_lt
end AspisR1.RRMessageRecoveryLaw
