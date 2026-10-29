import R0Z.MaskLayout
import R0Z.StatisticalDistance

/-! Z3: the original terminal is affine in H1, with semantic openings fixed.
Source: R0P/Copy.lean:111–142,234–238 and SemDecision.lean:43–49,73–80.
The literal copy registry remains opaque throughout these algebraic proofs. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.ViewAffine
open R0P R0P.SemSource Polynomial
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks
variable {K : Type} [Field K] {F : Subfield K}

theorem copyResidual_affine (row : CopyRowExtension K) (chi p q a : K) :
    copyResidual row (a*p+(1-a)*q) chi =
      a * copyResidual row p chi + (1-a) * copyResidual row q chi := by
  unfold copyResidual
  ring

theorem copyEvaluate_affine (o : Fin 16 → K) (s : CopySelectors K)
    (lam chi : K) (append : Nat) (variant : Variant) (p q a : K) :
    (copyEvaluateWithSelectors o (a*p+(1-a)*q) s lam chi append variant).1 =
      a * (copyEvaluateWithSelectors o p s lam chi append variant).1 +
      (1-a) * (copyEvaluateWithSelectors o q s lam chi append variant).1 := by
  simp only [copyEvaluateWithSelectors, copyResidual_affine]
  ring

theorem laneAt_affine (pub : Public K) (lam chi : K) (B : PackBasis F)
    (o : Openings K) (s : Sel K) (p q a : K) (i : Fin 29) :
    laneAt pub lam chi B o (a*p+(1-a)*q) s i =
      a * laneAt pub lam chi B o p s i + (1-a) * laneAt pub lam chi B o q s i := by
  unfold laneAt
  split_ifs
  · ring
  · ring
  · simp only [copyFamily, List.getD_cons_zero, copyEvaluate_affine]

/-- The soundness terminal with its sixteen semantic openings and H1 separated.
There is no change to the original's copy residual or theta-lane ordering. -/
def originalAt (pub : Public K) (lam chi theta mu : K) (zc : Fin 10 → K)
    (B : PackBasis F) (o : Openings K) (h : K) (alpha : Fin 10 → K) : K :=
  eqValue zc alpha * (∑ i : Fin 29, theta^i.val * laneAt pub lam chi B o h (selAt alpha) i) +
    mu*h + mu*mu*((1-activeAt alpha)*h)

theorem originalAt_affine (pub : Public K) (lam chi theta mu : K) (zc : Fin 10 → K)
    (B : PackBasis F) (o : Openings K) (alpha : Fin 10 → K) (p q a : K) :
    originalAt pub lam chi theta mu zc B o (a*p+(1-a)*q) alpha =
      a * originalAt pub lam chi theta mu zc B o p alpha +
      (1-a) * originalAt pub lam chi theta mu zc B o q alpha := by
  simp only [originalAt, laneAt_affine, mul_add]
  simp_rw [mul_left_comm (theta ^ _) a, mul_left_comm (theta ^ _) (1-a)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem originalAt_decomp (pub : Public K) (lam chi theta mu : K) (zc : Fin 10 → K)
    (B : PackBasis F) (o : Openings K) (alpha : Fin 10 → K) (h : K) :
    originalAt pub lam chi theta mu zc B o h alpha =
      originalAt pub lam chi theta mu zc B o 0 alpha +
        h * (originalAt pub lam chi theta mu zc B o 1 alpha -
          originalAt pub lam chi theta mu zc B o 0 alpha) := by
  have hh := originalAt_affine pub lam chi theta mu zc B o alpha 1 0 h
  simp only [mul_one, mul_zero, add_zero] at hh
  rw [hh]
  ring

/-- This identity uses the actual terminal, not an assumed affinity certificate. -/
theorem terminalValue_eq_originalAt (pub : Public K) (lam chi theta mu : K)
    (zc : Fin 10 → K) (B : PackBasis F) (y : Fin 3 → Fin 29 → K) (alpha : Fin 10 → K) :
    terminalValue pub lam chi theta mu zc B y alpha =
      originalAt pub lam chi theta mu zc B
        ⟨fun c => y 0 (Fin.castLE (by omega) c),
          fun c => y 1 (Fin.castLE (by omega) c),
          fun c => y 2 (Fin.castLE (by omega) c)⟩ (y 0 26) alpha := rfl

#print axioms copyResidual_affine
#print axioms laneAt_affine
#print axioms originalAt_affine
#print axioms originalAt_decomp
#print axioms terminalValue_eq_originalAt
end R0Z.ViewAffine
