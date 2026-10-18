import CompPolySplitTrial
import CantorZassenhausRetries

namespace AspisR1.CompPolySplitRetries
open CompPoly AspisR1.CompPolySplitTrial

/-- Bounded retries: exhausted coins return none. There is no enumeration
fallback; distinct recursion nodes must receive independent probe tapes. -/
def retry {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (q : Nat) :
    (t : Nat) → (Fin t → K × K) → Option (CPolynomial K)
  | 0, _ => none
  | t+1, tape =>
      match trySplit f (linear (tape 0)) q with
      | some d => some d
      | none => retry f q t (fun i => tape i.succ)

def retryFailure {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (q t : Nat) (tape : Fin t → K × K) : Rat :=
  if (retry f q t tape).isSome then 0 else 1

noncomputable section
open Polynomial AspisR1.CantorZassenhausRetries AspisR1.CantorZassenhausFastTrial
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem retryFailure_eq_product (f : CPolynomial K) (q t : Nat) (tape : Fin t → K × K) :
    retryFailure f q t tape = ∏ i, failure f q (tape i) := by
  induction t with
  | zero => simp [retryFailure, retry]
  | succ t ih =>
    rw [Fin.prod_univ_succ]
    cases h : trySplit f (linear (tape 0)) q with
    | none =>
      have hhead : failure f q (tape 0) = 1 := by simp [AspisR1.CompPolySplitTrial.failure, h]
      rw [hhead, one_mul]
      unfold retryFailure
      rw [retry, h]
      exact ih (fun i => tape i.succ)
    | some d =>
      have hhead : failure f q (tape 0) = 0 := by simp [AspisR1.CompPolySplitTrial.failure, h]
      rw [hhead, zero_mul]
      simp [retryFailure, retry, h]

theorem retryFailure_eq_allFail (f : CPolynomial K) (q t : Nat)
    (tape : Fin t → K × K) (hf : f.toPoly.Monic) :
    retryFailure f q t tape = allFail f.toPoly q t tape := by
  rw [retryFailure_eq_product]
  unfold allFail
  apply Finset.prod_congr rfl
  intro i _
  exact failure_eq_math f q (tape i) hf

theorem actual_retry_failure_le (f : CPolynomial K) (a b : K) (q t : Nat)
    (hq : q = Fintype.card K) (hf : f.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < degree f.toPoly) (hab : a ≠ b)
    (hodd : ringChar K ≠ 2) (ha : IsRoot f.toPoly a) (hb : IsRoot f.toPoly b) :
    (∑ tape : Fin t → K × K, retryFailure f q t tape) /
      (((q : Rat)^2)^t) ≤ (1/2)^t := by
  simp_rw [retryFailure_eq_allFail f q t _ hf]
  exact independent_retry_failure_le f.toPoly a b q t hq hf hdeg hab hodd ha hb

#print axioms retryFailure_eq_product
#print axioms retryFailure_eq_allFail
#print axioms actual_retry_failure_le
end
end AspisR1.CompPolySplitRetries
