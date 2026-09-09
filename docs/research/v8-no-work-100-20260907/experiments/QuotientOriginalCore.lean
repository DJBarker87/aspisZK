import OODInterpolantRows
import AspisFormal.V5FriCircleEncoderDistance

/-! Reconstruct an actual original-code message and account for possible
chord poles. The received word is arbitrary; no global inverse premise is
silently inferred from the verifier's queried denominator checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 12000
namespace AspisV8.OODInterpolant
noncomputable section
open Polynomial AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisV8.InterleavedChordLinear AspisV8.InterleavedChordRows
open AspisV8.ChordPolynomialImage
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

theorem naturalPolynomial_add {n : Nat} (hn : 0<n) (u v : Fin n → K) :
    naturalCoefficientPolynomial (u+v)=
      naturalCoefficientPolynomial u+naturalCoefficientPolynomial v := by
  rw [line_polynomial hn,line_polynomial hn,line_polynomial hn]
  exact (lineLinear n).map_add u v

theorem circle_message_add (u v : Fin 1024 → K) (x y : K) :
    circleEval (initialP0 (u+v)) (initialP1 (u+v)) x y=
      circleEval (initialP0 u) (initialP1 u) x y+
      circleEval (initialP0 v) (initialP1 v) x y := by
  have he : evenCoefficients (n := 512) (u+v)=
      evenCoefficients (n := 512) u+evenCoefficients (n := 512) v := rfl
  have ho : oddCoefficients (n := 512) (u+v)=
      oddCoefficients (n := 512) u+oddCoefficients (n := 512) v := rfl
  simp only [circleEval,initialP0,initialP1,he,ho,
    naturalPolynomial_add (by decide : 0<512),eval_add]
  ring

def Data.original (d : Data (K := K)) (Q : Fin 1024 → K) : Fin 1024 → K :=
  reconstruction d.a d.b d.c Q+d.interpolant

theorem Data.original_eq_rows (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 4 → K) (Q : Fin 1024 → K) :
    d.original Q=(d.rows quarter w claimed Q).reconstruction Q+
      (d.rows quarter w claimed Q).interpolant := rfl

/-- The actual two-entry interpolant and the total natural projection are
used, including the equal-x OOD branch. No transpose/evaluation equality is
a premise. Image validity is the literal pair of top coefficient equations. -/
theorem Data.original_eval (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (x y : K) (circle : x^2+y^2=1) :
    circleEval (initialP0 (d.original Q)) (initialP1 (d.original Q)) x y=
      (d.a+d.b*x+d.c*y)*circleEval (initialP0 Q) (initialP1 Q) x y+
        circleEval (initialP0 d.interpolant) (initialP1 d.interpolant) x y := by
  rw [Data.original,circle_message_add]
  rw [message_circle_eval d.a d.b d.c x y Q (d.chord_nondegenerate checked) image circle]

def chordNumerator (a b c : K) : K[X] := monomialPolynomial ![a+b,2*c,a-b]

theorem chordNumerator_eval (a b c t : K) :
    (chordNumerator a b c).eval t=(a+b)+2*c*t+(a-b)*t^2 := by
  simp [chordNumerator,monomialPolynomial,Fin.sum_univ_succ]
  ring

theorem chordNumerator_degree (a b c : K) : (chordNumerator a b c).natDegree≤2 :=
  monomialPolynomial_natDegree_le (by decide) _

theorem chordNumerator_nonzero (a b c : K) (nondegenerate : b≠0 ∨ c≠0) :
    chordNumerator a b c≠0 := by
  intro zero
  have hcfs (j : Fin 3) : (![a+b,2*c,a-b] : Fin 3 → K) j=0 := by
    simpa only [chordNumerator,monomialPolynomial_coeff,coeff_zero] using
      congrArg (fun p : K[X] => p.coeff j.val) zero
  have h0 : a+b=0 := hcfs 0
  have h1 : (2:K)*c=0 := hcfs 1
  have h2 : a-b=0 := hcfs 2
  have hc : c=0 := (mul_eq_zero.mp h1).resolve_left (NeZero.ne (2:K))
  have hb2 : (2:K)*b=0 := by linear_combination h0-h2
  have hb : b=0 := (mul_eq_zero.mp hb2).resolve_left (NeZero.ne (2:K))
  exact nondegenerate.elim (fun h=>h hb) (fun h=>h hc)

/-- Degree two after stereographic substitution, not the older generic
degree1024 initial-code cap. The existing circle identities provide the
nonzero clearing denominator. -/
theorem chordNumerator_stereo (a b c x y : K) (circle : x^2+y^2=1)
    (west : x≠-1) :
    (chordNumerator a b c).eval (y/(1+x))=
      (1+(y/(1+x))^2)*(a+b*x+c*y) := by
  obtain ⟨hn,hx,hy⟩ := AspisV5FriCircleEncoderDistance.stereo_identities x y circle west
  have xx := (div_eq_iff hn).mp hx
  have yy := (div_eq_iff hn).mp hy
  rw [chordNumerator_eval]
  linear_combination b*xx+c*yy

#print axioms circle_message_add
#print axioms Data.original_eq_rows
#print axioms Data.original_eval
#print axioms chordNumerator_nonzero
#print axioms chordNumerator_stereo
end
end AspisV8.OODInterpolant
