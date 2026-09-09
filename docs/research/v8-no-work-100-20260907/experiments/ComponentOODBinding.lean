import QuotientOriginalCore
import ClaimTransport
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! The actual two OOD answer vectors bind the reconstructed message at
their two circle points. Individual correctness is NOT assumed. A recovered
component tuple gives a degree28 error polynomial vanishing at gamma.
Using that vanishing as a probability bound still requires the tuple, point
and answer vector to be fixed before a genuinely fresh gamma. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 12000
namespace AspisV8.ComponentOODBinding
noncomputable section
open Polynomial
open AspisV5FriInitialCircleEncoderIdentity
open AspisV8.InterleavedChordLinear AspisV8.ChordPolynomialImage
open AspisV8.NaturalChordImage
open AspisV8.OODInterpolant AspisV8.ClaimTransport
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

/-- A genuine linear functional, built from the actual low-bit circle
tensor encoder rather than an assumed evaluation linearity predicate. -/
def circleFunctional (x y : K) : (Fin 1024 → K) →ₗ[K] K :=
  (Polynomial.leval x).comp ((lineLinear 512).comp (evenLinear 512))+
    y • (Polynomial.leval x).comp ((lineLinear 512).comp (oddLinear 512))

theorem circleFunctional_apply (x y : K) (message : Fin 1024 → K) :
    circleFunctional x y message=
      circleEval (initialP0 message) (initialP1 message) x y := by
  have hp0 : initialP0 message=line (evenCoefficients (n := 512) message) := by
    unfold initialP0
    exact line_polynomial (K := K) (n := 512) (by decide) _
  have hp1 : initialP1 message=line (oddCoefficients (n := 512) message) := by
    unfold initialP1
    exact line_polynomial (K := K) (n := 512) (by decide) _
  rw [hp0,hp1]
  simp only [circleFunctional,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,Polynomial.leval_apply,smul_eq_mul,
    lineLinear_apply,evenLinear_apply (K := K) (n := 512) message,
    oddLinear_apply (K := K) (n := 512) message,circleEval]

def pointX (d : Data (K := K)) : Fin 2 → K := ![d.x0,d.x1]
def pointY (d : Data (K := K)) : Fin 2 → K := ![d.y0,d.y1]

/-- The chord vanishes at its two defining points. The checked source
interpolant evaluates to its gamma batches, including the equal-x branch. -/
theorem original_point_values (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1) (r : Fin 2) :
    circleFunctional (pointX d r) (pointY d r) (d.original Q)=d.batch r := by
  have h0 : circleFunctional d.x0 d.y0 (d.original Q)=d.batch 0 := by
    rw [circleFunctional_apply,d.original_eval checked Q image d.x0 d.y0 circles.1,
      d.chord_at_points.1,zero_mul,zero_add]
    exact (d.eval_at_points checked).1
  have h1 : circleFunctional d.x1 d.y1 (d.original Q)=d.batch 1 := by
    rw [circleFunctional_apply,d.original_eval checked Q image d.x1 d.y1 circles.2,
      d.chord_at_points.2,zero_mul,zero_add]
    exact (d.eval_at_points checked).2
  fin_cases r
  · exact h0
  · exact h1

/-- No individual OOD answer is declared correct: the derived scalar-power
error polynomial must vanish at the actual gamma once recovery identifies
the reconstructed original message. -/
theorem recovered_ood_error_eval (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (p : Fin 29 → Fin 1024 → K)
    (recovered : d.original Q=ClaimTransport.batch d.gamma p) (r : Fin 2) :
    (errorPolynomial (circleFunctional (pointX d r) (pointY d r)) p
      (d.answers r)).eval d.gamma=0 := by
  rw [← component_error_eval,← recovered]
  rw [original_point_values d checked Q image circles r]
  exact sub_self _

theorem ood_error_degree (d : Data (K := K)) (p : Fin 29 → Fin 1024 → K) (r : Fin 2) :
    (errorPolynomial (circleFunctional (pointX d r) (pointY d r)) p
      (d.answers r)).natDegree≤28 := component_error_degree _ _ _

theorem ood_error_nonzero (d : Data (K := K)) (p : Fin 29 → Fin 1024 → K)
    (r : Fin 2) (lane : Fin 29)
    (wrong : d.answers r lane≠circleEval (initialP0 (p lane)) (initialP1 (p lane))
      (pointX d r) (pointY d r)) :
    errorPolynomial (circleFunctional (pointX d r) (pointY d r)) p (d.answers r)≠0 := by
  apply component_error_nonzero _ _ _ lane
  simpa only [circleFunctional_apply] using wrong

#print axioms circleFunctional_apply
#print axioms original_point_values
#print axioms recovered_ood_error_eval
#print axioms ood_error_degree
#print axioms ood_error_nonzero
end
end AspisV8.ComponentOODBinding
