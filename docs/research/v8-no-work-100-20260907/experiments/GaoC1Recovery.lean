import GaoRecovery
import CircleLaurentRecovery
import Mathlib.Data.Matrix.Mul

namespace AspisV8.GaoC1Recovery
open Polynomial Finset Matrix
open AspisV8.CircleLaurentRecovery
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
abbrev Row := Fin 1024
abbrev Bits := Row → Fin 10 → Bool

def value (bits : Bits) (coeff : Row → K) (x y : K) : K :=
  ∑ r, coeff r * ∏ j, if bits r j then coordinate x y j else 1

def evaluationMatrix (bits : Bits) (xs ys : Row → K) : Matrix Row Row K :=
  fun j r => ∏ b, if bits r b then coordinate (xs j) (ys j) b else 1

def recover {n : ℕ} (bits : Bits) (i : K) (xs ys received : Fin n → K)
    (tx ty : Row → K) (B : Matrix Row Row K) : Option (Row → K) :=
  (GaoRecovery.decode (fun j => xs j+i*ys j)
    (fun j => (xs j+i*ys j)^512*received j) 1025).map
    fun P => B *ᵥ (fun j => P.eval (tx j+i*ty j)/(tx j+i*ty j)^512)

/-- Complete coefficient recovery from arbitrary received samples within the
declared radius. No preselected returned P, decoder success, honest received
polynomial or witness-validity premise is used. The inverse is public. -/
theorem recover_coefficients {n : ℕ} (hn : 1025≤n)
    (i h g : K) (hi : i^2 = -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Bits) (coeff : Row → K) (xs ys received : Fin n → K)
    (circles : ∀ j, (xs j)^2+(ys j)^2=1)
    (distinct : Function.Injective (fun j => xs j+i*ys j))
    (close : (univ.filter fun j => value bits coeff (xs j) (ys j)≠received j).card≤(n-1025)/2)
    (tx ty : Row → K) (targetCircles : ∀ j, (tx j)^2+(ty j)^2=1)
    (B : Matrix Row Row K) (inverse : B*evaluationMatrix bits tx ty=1) :
    recover bits i xs ys received tx ty B=some coeff := by
  obtain ⟨P,degreeP,evalP⟩ := natural_tensor_embedding i h g hi hh hg bits coeff
  have errs : GaoRecovery.errors (fun j => xs j+i*ys j)
      (fun j => (xs j+i*ys j)^512*received j) P =
      univ.filter (fun j => value bits coeff (xs j) (ys j)≠received j) := by
    unfold GaoRecovery.errors
    apply Finset.filter_congr
    intro j _
    have nonzero : (xs j+i*ys j)^512≠0 := pow_ne_zero _ (circle_z_nonzero _ _ _ hi (circles j))
    rw [evalP _ _ (circles j)]
    change _≠_ ↔ value bits coeff (xs j) (ys j)≠received j
    exact not_congr (mul_right_inj' nonzero)
  have decoded := GaoRecovery.decoder_complete (by decide : 0<1025) hn
    (fun j => xs j+i*ys j) (fun j => (xs j+i*ys j)^512*received j)
    distinct P (by omega) (by simpa [errs] using close)
  have unscaled : (fun j => P.eval (tx j+i*ty j)/(tx j+i*ty j)^512) =
      evaluationMatrix bits tx ty *ᵥ coeff := by
    funext j
    have nonzero : (tx j+i*ty j)^512≠0 := pow_ne_zero _ (circle_z_nonzero _ _ _ hi (targetCircles j))
    rw [evalP _ _ (targetCircles j),mul_div_cancel_left₀ _ nonzero]
    simp only [Matrix.mulVec, dotProduct, evaluationMatrix]
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _
  simp only [recover,decoded,Option.map_some,unscaled]
  rw [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec]

#print axioms recover_coefficients
end
end AspisV8.GaoC1Recovery
