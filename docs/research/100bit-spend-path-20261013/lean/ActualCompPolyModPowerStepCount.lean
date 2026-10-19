import CompPolyPolynomialBackendBridge
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

namespace ActualCompPolyModPowerStepCount
open CompPoly AspisR1.CompPolyPolynomialBackendBridge

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- The actual binary-recursive modular powering term with a ghost count of
the two polynomial multiplications and one remainder at each non-base digit. -/
def modPowerValueStep (a m : CPolynomial K) (b : Bool)
    (z : CPolynomial K) : CPolynomial K :=
  (z * z * (if b then a else 1)).modByMonic m

def modPowerCountedStep (a m : CPolynomial K) (b : Bool) (n : Nat)
    (z : CPolynomial K × Nat) : CPolynomial K × Nat :=
  (modPowerValueStep a m b z.1,
    if b = false ∧ n = 0 then z.2 else z.2 + 3)

def modPowerWithSteps (a m : CPolynomial K) : Nat → CPolynomial K × Nat :=
  Nat.binaryRec (1, 0) (modPowerCountedStep a m)

theorem modPowerWithSteps_value (a m : CPolynomial K) (e : Nat) :
    (modPowerWithSteps a m e).1 = modPower a m e := by
  refine Nat.binaryRec (motive := fun n =>
    (modPowerWithSteps a m n).1 = modPower a m n) ?_ ?_ e
  · rfl
  · intro b n ih
    by_cases hzero : b = false ∧ n = 0
    · rcases hzero with ⟨rfl, rfl⟩
      rfl
    · have hcond : n = 0 → b = true := by
        intro hn
        subst n
        cases b
        · exact (hzero ⟨rfl, rfl⟩).elim
        · rfl
      rw [modPowerWithSteps, modPower]
      rw [Nat.binaryRec_eq b n (Or.inr hcond),
        Nat.binaryRec_eq b n (Or.inr hcond)]
      simp only [modPowerCountedStep, modPowerValueStep]
      simp only [modPowerWithSteps, modPower] at ih ⊢
      rw [ih]

theorem modPowerWithSteps_le_log (a m : CPolynomial K) (e : Nat) :
    (modPowerWithSteps a m e).2 ≤ 3 * (Nat.log2 e + 1) := by
  refine Nat.binaryRec (motive := fun n =>
    (modPowerWithSteps a m n).2 ≤ 3 * (Nat.log2 n + 1)) ?_ ?_ e
  · simp [modPowerWithSteps]
  · intro b n ih
    by_cases hzero : b = false ∧ n = 0
    · rcases hzero with ⟨rfl, rfl⟩
      simp [modPowerWithSteps]
    · have hcond : n = 0 → b = true := by
        intro hn
        subst n
        cases b
        · exact (hzero ⟨rfl, rfl⟩).elim
        · rfl
      rw [modPowerWithSteps]
      rw [Nat.binaryRec_eq b n (Or.inr hcond)]
      simp only [modPowerCountedStep]
      simp only [modPowerWithSteps] at ih
      simp only [if_neg hzero]
      by_cases hn : n = 0
      · subst n
        cases b with
        | false => exact (hzero ⟨rfl, rfl⟩).elim
        | true => norm_num [Nat.bit, ih]
      · have hbit2 : 2 ≤ Nat.bit b n := by
          cases b <;> simp [Nat.bit] <;> omega
        have hshift : Nat.bit b n / 2 = n := by
          cases b <;> simp [Nat.bit] <;> omega
        have hlog : Nat.log2 (Nat.bit b n) = Nat.log2 n + 1 := by
          rw [Nat.log2_def, if_pos hbit2, hshift]
        simp only [hlog]
        omega

#print axioms modPowerWithSteps_value
#print axioms modPowerWithSteps_le_log
end ActualCompPolyModPowerStepCount
