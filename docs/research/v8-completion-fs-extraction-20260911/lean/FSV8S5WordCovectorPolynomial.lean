import FSV8S5CompactPolynomialTarget

/-!
S5 FIRST ATTEMPT, UNCOMPILED. The coefficient/covector construction documented
in aspis-core/src/sumcheck.rs. Builds the reference polynomial rather than
accepting an opaque evaluator. This is algebra, not candidate-word availability,
Rust refinement, source-locality, or an extraction theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
namespace AspisV8Completion.FSV8S5WordCovectorPolynomial
open Polynomial FSV8S5CompactPolynomialTarget
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
abbrev Quad (K : Type*) := Fin 4 → K

def dot4 (a b : Quad K) : K := a 0*b 0+a 1*b 1+a 2*b 2+a 3*b 3

def primal4 (a : Quad K) (x : K) : K :=
  a 0+x*(a 1+x*(a 2+x*a 3))

def dual4 (quarter : K) (b : Quad K) (x : K) : K :=
  quarter*(b 0+x*(b 3+x*(b 2+x*b 1)))

def pairCoefficients (quarter : K) (a b : Quad K) : Coeff7 K := ![
  quarter*(a 0*b 0),
  quarter*(a 0*b 3+a 1*b 0),
  quarter*(a 0*b 2+a 1*b 3+a 2*b 0),
  quarter*(a 0*b 1+a 1*b 2+a 2*b 3+a 3*b 0),
  quarter*(a 1*b 1+a 2*b 2+a 3*b 3),
  quarter*(a 2*b 1+a 3*b 2),
  quarter*(a 3*b 1)]

theorem pair_polynomial_evaluation (quarter : K) (a b : Quad K) (x : K) :
    (poly7 (pairCoefficients quarter a b)).eval x = primal4 a x*dual4 quarter b x := by
  simp [pairCoefficients, poly7, hstep, primal4, dual4] <;> ring

theorem pair_boundary (quarter : K) (a b : Quad K) :
    pairCoefficients quarter a b 0+pairCoefficients quarter a b 4 =
      quarter*dot4 a b := by
  simp [pairCoefficients, dot4] <;> ring

def coefficientsAdd (a b : Coeff7 K) : Coeff7 K := fun i => a i+b i

theorem poly7_add (a b : Coeff7 K) :
    poly7 (coefficientsAdd a b) = poly7 a+poly7 b := by
  simp [poly7, hstep, coefficientsAdd, Polynomial.C_add] <;> ring

/-- Chunks must come from one actual coefficient word and its actual covector,
using the same arity-four index order. No hidden word is manufactured here. -/
def wordCoefficients (quarter : K) : List (Quad K × Quad K) → Coeff7 K
  | [] => fun _ => 0
  | (a,b) :: rest => coefficientsAdd (pairCoefficients quarter a b)
      (wordCoefficients quarter rest)

def wordDot : List (Quad K × Quad K) → K
  | [] => 0
  | (a,b) :: rest => dot4 a b+wordDot rest

def foldedWordDot (quarter x : K) : List (Quad K × Quad K) → K
  | [] => 0
  | (a,b) :: rest => primal4 a x*dual4 quarter b x+foldedWordDot quarter x rest

theorem word_polynomial_evaluation (quarter x : K) : ∀ chunks,
    (poly7 (wordCoefficients quarter chunks)).eval x = foldedWordDot quarter x chunks := by
  intro chunks
  induction chunks with
  | nil => simp [wordCoefficients, foldedWordDot, poly7, hstep]
  | cons pair rest ih =>
      rcases pair with ⟨a,b⟩
      simp only [wordCoefficients, poly7_add, Polynomial.eval_add, foldedWordDot]
      rw [pair_polynomial_evaluation, ih]

theorem word_boundary (quarter : K) : ∀ chunks,
    wordCoefficients quarter chunks 0+wordCoefficients quarter chunks 4 =
      quarter*wordDot chunks := by
  intro chunks
  induction chunks with
  | nil => simp [wordCoefficients, wordDot]
  | cons pair rest ih =>
      rcases pair with ⟨a,b⟩
      change (pairCoefficients quarter a b 0+wordCoefficients quarter rest 0)+
          (pairCoefficients quarter a b 4+wordCoefficients quarter rest 4) =
        quarter*(dot4 a b+wordDot rest)
      calc
        _ = (pairCoefficients quarter a b 0+pairCoefficients quarter a b 4)+
            (wordCoefficients quarter rest 0+wordCoefficients quarter rest 4) := by ring
        _ = quarter*dot4 a b+quarter*wordDot rest := by rw [pair_boundary, ih]
        _ = _ := by ring

theorem word_boundary_exact (quarter : K) (fourQuarter : (4:K)*quarter=1)
    (chunks : List (Quad K × Quad K)) :
    (4:K)*(wordCoefficients quarter chunks 0+wordCoefficients quarter chunks 4) =
      wordDot chunks := by
  rw [word_boundary, ← mul_assoc, fourQuarter, one_mul]

/-- A genuinely false incoming claim excludes the identically-zero discrepancy
against this word. This is the point of retaining the boundary, not only the
degree bound. Source construction of the candidate word remains independent. -/
theorem different_claim_excludes_equal_coefficients
    (quarter claim : K) (fourQuarter : (4:K)*quarter=1)
    (sent : SameBodyRelation.Sent K) (chunks : List (Quad K × Quad K))
    (falseClaim : claim ≠ wordDot chunks) :
    SameBodyRelation.compact (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic
      claim sent ≠ wordCoefficients quarter chunks := by
  intro eqCoefficients
  have at0 := congrFun eqCoefficients 0
  have at4 := congrFun eqCoefficients 4
  have compactBoundary : (4:K)*(
      SameBodyRelation.compact (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic
        claim sent 0+
      SameBodyRelation.compact (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic
        claim sent 4) = claim := by
    simp [SameBodyRelation.compact, SameBodyQueryClaimExact.ringArithmetic]
    calc
      (4:K)*(claim*quarter) = ((4:K)*quarter)*claim := by ring
      _ = claim := by rw [fourQuarter, one_mul]
  apply falseClaim
  calc
    claim = (4:K)*(wordCoefficients quarter chunks 0+wordCoefficients quarter chunks 4) := by
      rw [← at0, ← at4]
      exact compactBoundary.symm
    _ = wordDot chunks := word_boundary_exact quarter fourQuarter chunks

#print axioms pair_polynomial_evaluation
#print axioms word_polynomial_evaluation
#print axioms word_boundary_exact
#print axioms different_claim_excludes_equal_coefficients
end
end AspisV8Completion.FSV8S5WordCovectorPolynomial
