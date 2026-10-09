import ChordRationalAlgebra
import ComponentOODBinding

/-! A reconstructed polynomial chord quotient forces both gamma-batched OOD
answers to be correct for the SAME original message.  The four radial lanes
are constructed from the actual y-low-bit natural coefficient convention.
No image, quotient-degree, nonpole-at-OOD or individual-answer premise is
needed.  Obtaining the reconstructed product identity is a separate upstream
theorem; this leaf does not assume it follows from verifier acceptance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalOOD
noncomputable section
open Polynomial AspisCircleTensorBinding
open AspisV5FriConcreteEncoderCommutation AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity AspisV5ComponentCConcreteFoldLinearity
open AspisV8.ChordRationalAlgebra AspisV8.ComponentOODBinding
open AspisV8.OODInterpolant
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

/-- The smaller natural encoder uses T2(x)=2*x²-1, whereas the cleared
four-component algebra uses radial coordinate x².  This is the explicit
affine substitution, not a change of the committed coefficient basis. -/
def radialLanes (message : Fin 1024 → K) : Fin 4 → K[X] :=
  fun j => (naturalCoefficientPolynomial (coefficientLane 256 j message)).comp
    (C 2*X-1)

theorem radial_lane_eval (message : Fin 1024 → K) (j : Fin 4) (x : K) :
    (radialLanes message j).eval (x^2)=
      (naturalCoefficientPolynomial (coefficientLane 256 j message)).eval
        (doubledFactor x 1) := by
  simp only [radialLanes,eval_comp,eval_sub,eval_mul,eval_C,eval_X,eval_one,
    doubledFactor]

/-- All four lanes are identified with the literal original-code circle
functional, including the source [1,y,x,xy] ordering. -/
theorem radial_lanes_value (message : Fin 1024 → K) (x y : K) :
    value x y (fun j => (radialLanes message j).eval (x^2))=
      circleFunctional x y message := by
  rw [circleFunctional_apply]
  unfold value AspisV8.ChordPolynomialImage.circleEval
  rw [initialP0_eval_lanes,initialP1_eval_lanes]
  simp only [radial_lane_eval]
  ring

theorem product_eval (s t : K[X]) (u v : Fin 4 → K[X]) (z : K) :
    (fun j => (product s t u v j).eval z)=
      product (s.eval z) (t.eval z) (fun j => (u j).eval z)
        (fun j => (v j).eval z) := by
  funext j
  fin_cases j <;> simp [product]

theorem line_eval (a b c z : K) :
    (fun j => (line (C a) (C b) (C c) j).eval z)=line a b c := by
  funext j
  fin_cases j <;> simp [line]

/-- This evaluates a genuine polynomial-vector identity even when the chord
or its norm vanishes at the evaluation point. There is no division here. -/
theorem reconstructed_value (message : Fin 1024 → K) (a b c x y : K)
    (q : Fin 4 → K[X]) (circle : x^2+y^2=1)
    (reconstructed : radialLanes message=
      product X (1-X) q (line (C a) (C b) (C c))) :
    circleFunctional x y message=
      value x y (fun j => (q j).eval (x^2))*(a+b*x+c*y) := by
  rw [←radial_lanes_value,reconstructed,product_eval,line_eval]
  have ht : ((1-X : K[X]).eval (x^2))=y^2 := by
    simp only [eval_sub,eval_one,eval_X]
    linear_combination -circle
  rw [eval_X,ht,product_value (x^2) (y^2) x y rfl rfl,line_value]

/-- Correctness of the two BATCHED answers follows without assuming image
validity. In particular the OOD points themselves are legal chord zeros. -/
theorem reconstructed_batched_ood (d : Data (K := K)) (checked : d.Checked)
    (U : Fin 1024 → K) (q : Fin 4 → K[X])
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (reconstructed : radialLanes (U-d.interpolant)=
      product X (1-X) q (line (C d.a) (C d.b) (C d.c))) :
    circleFunctional d.x0 d.y0 U=d.batch 0 ∧
      circleFunctional d.x1 d.y1 U=d.batch 1 := by
  have zero0 := reconstructed_value (U-d.interpolant) d.a d.b d.c
    d.x0 d.y0 q circles.1 reconstructed
  have zero1 := reconstructed_value (U-d.interpolant) d.a d.b d.c
    d.x1 d.y1 q circles.2 reconstructed
  rw [d.chord_at_points.1,mul_zero,map_sub] at zero0
  rw [d.chord_at_points.2,mul_zero,map_sub] at zero1
  have values := d.eval_at_points checked
  have val0 : circleFunctional d.x0 d.y0 d.interpolant=d.batch 0 := by
    rw [circleFunctional_apply]
    exact values.1
  have val1 : circleFunctional d.x1 d.y1 d.interpolant=d.batch 1 := by
    rw [circleFunctional_apply]
    exact values.2
  refine ⟨?_,?_⟩
  · exact (sub_eq_zero.mp zero0).trans val0
  · exact (sub_eq_zero.mp zero1).trans val1

#print axioms radial_lane_eval
#print axioms radial_lanes_value
#print axioms product_eval
#print axioms line_eval
#print axioms reconstructed_value
#print axioms reconstructed_batched_ood
end
end AspisV8.ChordRationalOOD
