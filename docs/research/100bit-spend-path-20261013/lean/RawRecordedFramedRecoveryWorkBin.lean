import BinEagerFramedRecoveryWork
import RawRecordedRecoveryWorkBin
import RawRecordedEagerReadPolynomialBin
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Eager extractor value refinement with recovery and frame-replay
comparison work. This remains a partial metric: it does not certify the
complete Resources ledger or public parsing, frame construction, GS or bits. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordedFramedRecoveryWorkBin
open RawRecordedEagerExtractorReadsBin
open AspisV8R19.OracleResampling
open SpendRelation FS

def eval (run : RunView) (coins : Coins) : Option Wspend × Nat :=
  optionReads (RawCutWordsFromRunPublicValidBin.runDecodedPublic run) fun decoded =>
    let cached := BinEagerFramedRecoveryWork.stage run
    (continueWithWords decoded cached.1 coins, cached.2)

attribute [local irreducible] continueWithWords BinEagerFramedRecoveryWork.stage
  BinEagerWordsReads.words GSByteJointSpendExtractor.extract

theorem value (run : RunView) (coins : Coins) :
    (eval run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  change (optionReads (RawCutWordsFromRunPublicValidBin.runDecodedPublic run)
    (fun decoded => (continueWithWords decoded (BinEagerFramedRecoveryWork.stage run).1 coins,
      (BinEagerFramedRecoveryWork.stage run).2))).1 = _
  rw [optionReads_value]
  simp only [BinEagerFramedRecoveryWork.stage_value]
  have h := RawRecordedRecoveryWorkBin.value run coins
  unfold RawRecordedRecoveryWorkBin.eval at h
  rw [optionReads_value] at h
  exact h

theorem work (run : RunView) (coins : Coins) :
    (eval run coins).2 ≤ 1000100000000 * (run.1.length + 1) :=
  optionReads_bound _ _ _ (fun _ => BinEagerFramedRecoveryWork.stage_work run)

def recoveryPolynomial : Polynomial Nat :=
  Polynomial.C 1000100000000 * (Polynomial.X + Polynomial.C 1162)

theorem polynomial_eval (Q : Nat) :
    recoveryPolynomial.eval Q = 1000100000000 * (Q + 1162) := by
  simp only [recoveryPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]

theorem polynomial_degree : recoveryPolynomial.natDegree ≤ 1 := by
  unfold recoveryPolynomial
  calc
    _ ≤ (Polynomial.C (1000100000000 : Nat)).natDegree +
        (Polynomial.X + Polynomial.C (1162 : Nat)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (Polynomial.C (1000100000000 : Nat)).natDegree +
        max (Polynomial.X : Polynomial Nat).natDegree (Polynomial.C (1162 : Nat)).natDegree :=
      Nat.add_le_add_left (Polynomial.natDegree_add_le _ _) _
    _ = 1 := by simp

theorem uniform_work (run : RunView) (Q : Nat) (hlog : run.1.length ≤ Q + 1161) :
    (∀ coins, (eval run coins).2 ≤ recoveryPolynomial.eval Q) ∧
    mean (fun coins : Coins => ((eval run coins).2 : ℚ)) ≤
      (Nat.cast (recoveryPolynomial.eval Q) : ℚ) := by
  have hall (coins : Coins) : (eval run coins).2 ≤ recoveryPolynomial.eval Q := by
    rw [polynomial_eval]
    exact (work run coins).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))
  refine ⟨hall, ?_⟩
  calc
    _ ≤ mean (fun _ : Coins => (Nat.cast (recoveryPolynomial.eval Q) : ℚ)) := mean_mono (by
      intro coins
      exact_mod_cast hall coins)
    _ = _ := mean_const _

theorem returned_relation (run : RunView) (coins : Coins) (w : Wspend)
    (h : (eval run coins).1 = some w) : LiteralProtocol.relation run.2.1.1 w :=
  RawRecordedPublicSpendExtractorBin.returned_relation run coins w
    ((value run coins).symm.trans h)

#print axioms value
#print axioms work
#print axioms polynomial_eval
#print axioms polynomial_degree
#print axioms uniform_work
#print axioms returned_relation
end AspisR1.RawRecordedFramedRecoveryWorkBin
end
