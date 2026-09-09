import InterleavedChordFull
import ShiftedRowPrefix

/-! The total 1024-coordinate natural reconstruction is now an actual linear
map usable by the shifted causal row prefix. Image validity is needed only
for the polynomial evaluation identity, never to define the map or its
transpose. The sparse Rust carry-loop refinement remains separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 5000
namespace AspisV8.InterleavedChordRows
noncomputable section
open Polynomial AspisCircleTensorBinding
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriRelationCandidateBridge
open AspisV8.NaturalChordImage AspisV8.NaturalChordProjection
open AspisV8.ChordPolynomialImage AspisV8.InterleavedChordLinear
open AspisV8.ShiftedRowPrefix AspisV8.FirstImageDiscrepancy
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

theorem interleave_composition_apply {n : Nat} {V : Type*}
    [AddCommGroup V] [Module K V] (A B : V →ₗ[K] (Fin n → K)) (v : V) :
    ((interleaveLinear n).comp (A.prod B)) v=interleave (A v) (B v) := rfl

theorem literal_transpose_dot {n m : Nat}
    (L : (Fin n → K) →ₗ[K] (Fin m → K)) (w : Fin m → K) (q : Fin n → K) :
    candidateClaim (reify ((covector w).comp L)) q=candidateClaim w (L q) :=
  reify_dot ((covector w).comp L) q

/-- TOTAL natural projection of full chord multiplication, followed by the
literal y-low-bit interleaving. In particular this is defined on invalid
image inputs and is not monomial coefficient truncation. -/
def reconstruction (a b c : K) : (Fin 1024 → K) →ₗ[K] (Fin 1024 → K) :=
  (interleaveLinear 512).comp
    (((projectLinear 512 2).comp (fullEvenLinear a b c)).prod
      ((projectLinear 512 2).comp (fullOddLinear a b c)))

theorem reconstruction_apply (a b c : K) (q : Fin 1024 → K) :
    reconstruction a b c q=interleave (projectedEven a b c q) (projectedOdd a b c q) := by
  unfold reconstruction
  rw [interleave_composition_apply,LinearMap.comp_apply,LinearMap.comp_apply]
  rw [fullEvenLinear_apply,fullOddLinear_apply,projectLinear_apply,projectLinear_apply]
  rfl

theorem even_reconstruction (a b c : K) (q : Fin 1024 → K) :
    evenCoefficients (reconstruction a b c q)=projectedEven a b c q := by
  rw [reconstruction_apply,interleave_even]
theorem odd_reconstruction (a b c : K) (q : Fin 1024 → K) :
    oddCoefficients (reconstruction a b c q)=projectedOdd a b c q := by
  rw [reconstruction_apply,interleave_odd]

theorem message_circle_eval (a b c x y : K) (q : Fin 1024 → K)
    (chord : b ≠ 0 ∨ c ≠ 0)
    (image : q 1023=0 ∧ b*q 1022-c*q 1021=0)
    (circle : x^2+y^2=1) :
    circleEval (initialP0 (reconstruction a b c q))
      (initialP1 (reconstruction a b c q)) x y =
      (a+b*x+c*y)*circleEval (initialP0 q) (initialP1 q) x y := by
  have he : initialP0 q=line (even q) := line_polynomial (by decide) _
  have ho : initialP1 q=line (odd q) := line_polynomial (by decide) _
  rw [he,ho]
  unfold initialP0 initialP1
  rw [even_reconstruction,odd_reconstruction]
  exact selected_projected_circle_eval a b c x y q chord image circle

/-- Literal transpose coefficients are determined by applying the primal
map to coordinate vectors. They are not supplied as a correspondence input. -/
def transpose (a b c : K) (w : Fin 1024 → K) : Fin 1024 → K :=
  reify ((covector w).comp (reconstruction a b c))

theorem transpose_dot (a b c : K) (w q : Fin 1024 → K) :
    candidateClaim (transpose a b c w) q = candidateClaim w (reconstruction a b c q) := by
  unfold transpose
  exact literal_transpose_dot (reconstruction a b c) w q

theorem reconstruction_dot_split (a b c : K) (w q : Fin 1024 → K) :
    (∑ i, w i*reconstruction a b c q i)=
      (∑ j, evenCoefficients w j*projectedEven a b c q j)+
      (∑ j, oddCoefficients w j*projectedOdd a b c q j) := by
  rw [reconstruction_apply]
  exact @interleave_dot K _ _ 512 w (projectedEven a b c q) (projectedOdd a b c q)

/-- This is the source's full-product / zero-padded-covector pairing, even
for invalid images. No overflow coefficient is silently assumed zero. -/
theorem reconstruction_full_dot (a b c : K) (w q : Fin 1024 → K) :
    (∑ i, w i*reconstruction a b c q i)=
      (∑ j, pad 2 (evenCoefficients w) j*coefficients 514 (fullEven a b c q) j)+
      (∑ j, pad 2 (oddCoefficients w) j*coefficients 514 (fullOdd a b c q) j) := by
  rw [reconstruction_dot_split]
  unfold projectedEven projectedOdd projectLine
  rw [prefix_dot,prefix_dot]

def rows (a b c quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 4 → K) (q interpolant : Fin 1024 → K) : Rows (K := K) where
  original := w
  claimed := claimed
  reconstruction := reconstruction a b c
  interpolant := interpolant
  referenceQ := q
  quarter := quarter
  b := b
  c := c

/-- The concrete primal map supplies the existing shifted affine constructor.
Neither inactive exactness nor a transpose identity is assumed. -/
theorem concrete_before_prior (a b c quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 4 → K) (q interpolant : Fin 1024 → K) (kappa : K) :
    ((rows a b c quarter w claimed q interpolant).before kappa).prior =
      ((rows a b c quarter w claimed q interpolant).errorPolynomial).eval kappa :=
  AspisV8.ShiftedRowPrefix.before_prior (rows a b c quarter w claimed q interpolant) kappa

/-- The actual accepted slope-inverse guard implies nondegenerate chord
direction, including the legal equal-x branch. No probability is charged. -/
theorem checked_slope_chord (x0 y0 x1 y1 : K)
    (checked : (if x0 ≠ x1 then x0-x1 else y0-y1) ≠ 0) :
    y0-y1 ≠ 0 ∨ x1-x0 ≠ 0 := by
  by_cases h : x0 ≠ x1
  · exact Or.inr (sub_ne_zero.mpr (Ne.symm h))
  · exact Or.inl (by simpa only [if_neg h] using checked)

#print axioms fullEvenLinear_apply
#print axioms fullOddLinear_apply
#print axioms reconstruction_apply
#print axioms even_reconstruction
#print axioms odd_reconstruction
#print axioms message_circle_eval
#print axioms transpose_dot
#print axioms reconstruction_dot_split
#print axioms reconstruction_full_dot
#print axioms concrete_before_prior
#print axioms checked_slope_chord
end
end AspisV8.InterleavedChordRows
