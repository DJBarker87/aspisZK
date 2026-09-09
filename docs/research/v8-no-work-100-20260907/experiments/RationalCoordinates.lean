import ChordRationalDegree
import ChordRationalOOD

/-! Small symbolic interfaces for actual radial/final coordinate transport.
No concrete domain or field is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.RationalCoordinates
noncomputable section
open Polynomial AspisCircleTensorBinding AspisV5FriConcreteEncoderApplicability
open AspisV8.ChordRationalDegree AspisV8.ChordRationalOOD
variable {K : Type*} [Field K] [NeZero (2 : K)]

def radialPolynomial (p : K[X]) : K[X] := p.comp (C 2*X-1)

theorem radial_polynomial_eval (p : K[X]) (s : K) :
    (radialPolynomial p).eval s=p.eval (finalFromRadial s) := by
  simp only [radialPolynomial,eval_comp,eval_sub,eval_mul,eval_C,eval_X,
    eval_one,finalFromRadial]

theorem radial_polynomial_degree (p : K[X]) (d : Nat) (degree : p.natDegree≤d) :
    (radialPolynomial p).natDegree≤d := by
  have affine : (C (2:K)*X-1).natDegree≤1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le.trans (Nat.add_le_add (by simp) natDegree_X_le))
    · simp
  exact natDegree_comp_le.trans ((Nat.mul_le_mul degree affine).trans (by simp))

def radialFinal {n : Nat} (final : Fin n → K) : K[X] :=
  radialPolynomial (naturalCoefficientPolynomial final)

theorem radial_final_degree {n : Nat} (positive : 0<n) (final : Fin n → K) :
    (radialFinal final).natDegree≤n-1 :=
  radial_polynomial_degree _ _ (naturalCoefficientPolynomial_natDegree_le positive final)

theorem radial_lanes_degree [DecidableEq K] (message : Fin 1024 → K) (j : Fin 4) :
    (radialLanes message j).natDegree≤255 :=
  radial_polynomial_degree _ _
    (naturalCoefficientPolynomial_natDegree_le (by omega)
      (AspisV5FriConcreteEncoderCommutation.coefficientLane 256 j message))

theorem final_from_radial_inverse (z : K) :
    finalFromRadial (radialFromFinal z)=z := by
  unfold finalFromRadial radialFromFinal
  field_simp
  ring

theorem radial_from_final_injective : Function.Injective (radialFromFinal (K:=K)) := by
  intro a b equal
  have h := congrArg finalFromRadial equal
  simpa only [final_from_radial_inverse] using h

theorem indexed_matching_card_le {I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq K] (point : I → K) (injective : Function.Injective point)
    (matching : I → Prop) [DecidablePred matching] (allowed : Finset K)
    (inside : ∀ i, matching i → point i∈allowed) :
    (Finset.univ.filter matching).card≤allowed.card := by
  rw [←Finset.card_image_of_injective _ injective]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  exact inside i (Finset.mem_filter.mp hi).2

#print axioms radial_polynomial_eval
#print axioms radial_polynomial_degree
#print axioms radial_final_degree
#print axioms radial_lanes_degree
#print axioms final_from_radial_inverse
#print axioms radial_from_final_injective
#print axioms indexed_matching_card_le
end
end AspisV8.RationalCoordinates
