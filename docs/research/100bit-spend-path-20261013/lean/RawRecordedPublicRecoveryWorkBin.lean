import PublicParserWork
import BinPublicRecoveryStageWork
import RawRecordedEagerExtractorReadsBin
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Public parse, frame replay/construction, binary recovery and typed-word
materialization. The continuation is value-refined but remains uncharged here;
this is deliberately not an instance of the total Resources ledger. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordedPublicRecoveryWorkBin
open RawRecordedEagerExtractorReadsBin
open AspisV8R19.OracleResampling
open SpendRelation FS

def eval (run : RunView) (coins : Coins) : Option Wspend × Nat :=
  let parsed := PublicParserWork.parsePublic run.2.1.1.pubBytes
  PublicParserWork.bind parsed fun decoded =>
    let cached := BinPublicRecoveryStageWork.stage run
    (continueWithWords decoded cached.1 coins, cached.2)

attribute [local irreducible] continueWithWords BinPublicRecoveryStageWork.stage
  BinEagerWordsReads.words

theorem value (run : RunView) (coins : Coins) :
    (eval run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  simp only [eval, PublicParserWork.bind_value, PublicParserWork.parsePublic_value,
    BinPublicRecoveryStageWork.stage_value]
  have hv := RawRecordedEagerExtractorReadsBin.value run coins
  simpa only [RawRecordedEagerExtractorReadsBin.eval, optionReads_value,
    RawCutWordsFromRunPublicValidBin.runDecodedPublic] using hv

theorem work (run : RunView) (coins : Coins) :
    (eval run coins).2 ≤ 5000000000000*(run.1.length+1) := by
  have h := PublicParserWork.bind_work
    (PublicParserWork.parsePublic run.2.1.1.pubBytes)
    (fun decoded => (continueWithWords decoded (BinPublicRecoveryStageWork.stage run).1 coins,
      (BinPublicRecoveryStageWork.stage run).2))
    110260 (4000000000000*(run.1.length+1))
    (PublicParserWork.parsePublic_work _) (fun _ => BinPublicRecoveryStageWork.stage_work run)
  exact h.trans (by omega)

def costPolynomial : Polynomial Nat :=
  Polynomial.C 5000000000000 * (Polynomial.X+Polynomial.C 1162)

theorem polynomial_eval (Q : Nat) : costPolynomial.eval Q = 5000000000000*(Q+1162) := by
  simp only [costPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]

theorem polynomial_degree : costPolynomial.natDegree ≤ 1 := by
  have h := Polynomial.natDegree_mul_le (p := Polynomial.C (5000000000000 : Nat))
    (q := Polynomial.X+Polynomial.C (1162 : Nat))
  simp only [Polynomial.natDegree_C, Nat.zero_add] at h
  exact h.trans ((Polynomial.natDegree_add_le _ _).trans (by simp))

theorem uniform_work (run : RunView) (Q : Nat) (hlog : run.1.length ≤ Q+1161) :
    (∀ coins, (eval run coins).2 ≤ costPolynomial.eval Q) ∧
    mean (fun coins : Coins => ((eval run coins).2 : ℚ)) ≤
      (Nat.cast (costPolynomial.eval Q) : ℚ) := by
  have hall (coins : Coins) : (eval run coins).2 ≤ costPolynomial.eval Q := by
    rw [polynomial_eval]
    exact (work run coins).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))
  refine ⟨hall, ?_⟩
  calc
    _ ≤ mean (fun _ : Coins => (Nat.cast (costPolynomial.eval Q) : ℚ)) := mean_mono (by
      intro coins; exact_mod_cast hall coins)
    _ = _ := mean_const _

#print axioms value
#print axioms work
#print axioms polynomial_eval
#print axioms polynomial_degree
#print axioms uniform_work
end AspisR1.RawRecordedPublicRecoveryWorkBin
end
