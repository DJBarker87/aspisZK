import Mathlib.Tactic

/-! A secant to the affine circle has exactly its two specified circle
zeroes. This uses only a field of characteristic different from two. -/
set_option autoImplicit false
namespace AspisR0.ChordGeometry
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [NeZero (2 : K)]

abbrev Point (K : Type*) [Field K] := {z : K × K // z.1^2+z.2^2=1}

def line (a b c : K) (z : Point K) : K := a+b*z.1.1+c*z.1.2
def secantA (z0 z1 : Point K) : K := z0.1.1*z1.1.2-z1.1.1*z0.1.2
def secantB (z0 z1 : Point K) : K := z0.1.2-z1.1.2
def secantC (z0 z1 : Point K) : K := z1.1.1-z0.1.1
def secant (z0 z1 : Point K) : Point K → K :=
  line (secantA z0 z1) (secantB z0 z1) (secantC z0 z1)

theorem secant_zeroes (z0 z1 : Point K) : secant z0 z1 z0 = 0 ∧ secant z0 z1 z1 = 0 := by
  constructor <;> dsimp [secant, line, secantA, secantB, secantC] <;> ring

theorem secant_nontrivial (z0 z1 : Point K) (hne : z0 ≠ z1) :
    secantB z0 z1 ≠ 0 ∨ secantC z0 z1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  apply Subtype.ext
  exact Prod.ext (sub_eq_zero.mp h.2).symm (sub_eq_zero.mp h.1)

def intersectionPolynomial (a b c : K) : K[X] :=
  C (b^2+c^2)*X^2+C (2*a*b)*X+C (a^2-c^2)

theorem intersection_root (a b c : K) (z : Point K) (hz : line a b c z = 0) :
    (intersectionPolynomial a b c).eval z.1.1 = 0 := by
  simp only [intersectionPolynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  dsimp [line] at hz
  linear_combination c^2*z.property+(a+b*z.1.1-c*z.1.2)*hz

theorem intersection_nonzero (a b c : K) (hc : c ≠ 0) : intersectionPolynomial a b c ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : K[X] => p.coeff 0) h
  have h1 := congrArg (fun p : K[X] => p.coeff 1) h
  have h2 := congrArg (fun p : K[X] => p.coeff 2) h
  simp only [intersectionPolynomial, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at h0 h1 h2
  norm_num at h0 h1 h2
  have ha : a ≠ 0 := by
    intro hz
    apply hc
    apply sq_eq_zero_iff.mp
    simpa [hz] using h0.symm
  have hb : b = 0 := h1.resolve_left (not_or.mpr ⟨NeZero.ne _, ha⟩)
  apply hc
  apply sq_eq_zero_iff.mp
  simpa [hb] using h2

theorem line_x_injective (a b c : K) (hc : c ≠ 0) (z0 z1 : Point K)
    (h0 : line a b c z0 = 0) (h1 : line a b c z1 = 0)
    (hx : z0.1.1 = z1.1.1) : z0 = z1 := by
  apply Subtype.ext
  refine Prod.ext hx ?_
  apply mul_left_cancel₀ hc
  dsimp [line] at h0 h1
  rw [hx] at h0
  linear_combination h0-h1

theorem only_two_of_c_nonzero (a b c : K) (hc : c ≠ 0)
    (z0 z1 z : Point K) (hne : z0 ≠ z1)
    (h0 : line a b c z0 = 0) (h1 : line a b c z1 = 0) (hz : line a b c z = 0) :
    z = z0 ∨ z = z1 := by
  by_contra h
  push Not at h
  have h01 : z0.1.1 ≠ z1.1.1 := fun he => hne (line_x_injective a b c hc z0 z1 h0 h1 he)
  have hz0 : z.1.1 ≠ z0.1.1 := fun he => h.1 (line_x_injective a b c hc z z0 hz h0 he)
  have hz1 : z.1.1 ≠ z1.1.1 := fun he => h.2 (line_x_injective a b c hc z z1 hz h1 he)
  let nodes : Fin 3 → K := ![z0.1.1,z1.1.1,z.1.1]
  have hinj : Function.Injective nodes := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [nodes]
  have hdeg : (intersectionPolynomial a b c).natDegree ≤ 2 := by
    unfold intersectionPolynomial
    compute_degree
  apply intersection_nonzero a b c hc
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
  · intro i
    fin_cases i
    · exact intersection_root a b c z0 h0
    · exact intersection_root a b c z1 h1
    · exact intersection_root a b c z hz
  · simp only [Fintype.card_fin]
    omega

def swap (z : Point K) : Point K := ⟨(z.1.2,z.1.1), by simpa [add_comm] using z.property⟩

theorem swap_injective : Function.Injective (swap (K := K)) := by
  intro z w h
  apply Subtype.ext
  have hp := congrArg Subtype.val h
  exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

theorem secant_only_zeroes (z0 z1 : Point K) (hne : z0 ≠ z1) (z : Point K)
    (hz : secant z0 z1 z = 0) : z = z0 ∨ z = z1 := by
  obtain ⟨h0,h1⟩ := secant_zeroes z0 z1
  by_cases hc : secantC z0 z1 ≠ 0
  · exact only_two_of_c_nonzero _ _ _ hc z0 z1 z hne h0 h1 hz
  · have hb := (secant_nontrivial z0 z1 hne).resolve_right hc
    have transpose (p : Point K) :
        line (secantA z0 z1) (secantC z0 z1) (secantB z0 z1) (swap p) = secant z0 z1 p := by
      dsimp [line, swap, secant]
      ring
    have h := only_two_of_c_nonzero (secantA z0 z1) (secantC z0 z1) (secantB z0 z1)
      hb (swap z0) (swap z1) (swap z) (fun he => hne (swap_injective he))
      (by rw [transpose]; exact h0) (by rw [transpose]; exact h1) (by rw [transpose]; exact hz)
    exact h.elim (fun he => Or.inl (swap_injective he)) (fun he => Or.inr (swap_injective he))

#print axioms secant_nontrivial
#print axioms secant_only_zeroes
end
end AspisR0.ChordGeometry
