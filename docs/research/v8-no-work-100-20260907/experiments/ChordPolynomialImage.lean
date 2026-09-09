import AspisFormal.CircleNaturalBasis

/-! Coefficient reconstruction and the actual circle equation. This is a
polynomial/natural-basis interface, not an assumed transpose identity and not
a translated Rust encoder. No global polynomiality of received words is used. -/
set_option autoImplicit false
namespace AspisV8.ChordPolynomialImage
noncomputable section
open Polynomial AspisCircleTensorBinding
variable {K : Type*} [Field K]

def evenPart (a b c : K) (A B : K[X]) : K[X] :=
  C a*A + C b*(X*A) + C c*(B-X*(X*B))
def oddPart (a b c : K) (A B : K[X]) : K[X] :=
  C c*A + C a*B + C b*(X*B)
def circleEval (A B : K[X]) (x y : K) : K := A.eval x+y*B.eval x

/-- The circle equation is essential: at off-circle points the reconstructed
pair is generally not multiplication by the chord. -/
theorem chord_eval (a b c x y : K) (A B : K[X]) (circle : x^2+y^2=1) :
    circleEval (evenPart a b c A B) (oddPart a b c A B) x y =
      (a+b*x+c*y)*circleEval A B x y := by
  simp only [circleEval, evenPart, oddPart, eval_add, eval_sub, eval_mul, eval_C, eval_X]
  linear_combination -c*B.eval x*circle

theorem quotient_eq_reconstruction (a b c x y received : K)
    (A B IA IB : K[X]) (circle : x^2+y^2=1) (denom : a+b*x+c*y ≠ 0) :
    (received-circleEval IA IB x y)/(a+b*x+c*y) = circleEval A B x y ↔
      received = circleEval (evenPart a b c A B+IA) (oddPart a b c A B+IB) x y := by
  have ev : circleEval (evenPart a b c A B+IA) (oddPart a b c A B+IB) x y =
      (a+b*x+c*y)*circleEval A B x y+circleEval IA IB x y := by
    rw [circleEval, eval_add, eval_add]
    have h := chord_eval a b c x y A B circle
    dsimp [circleEval] at h ⊢
    linear_combination h
  rw [ev, div_eq_iff denom]
  constructor <;> intro h <;> linear_combination h

theorem even_coeff (a b c : K) (A B : K[X]) (n : Nat) :
    (evenPart a b c A B).coeff (n+2) =
      a*A.coeff (n+2)+b*A.coeff (n+1)+c*(B.coeff (n+2)-B.coeff n) := by
  simp [evenPart, coeff_X_mul]

theorem odd_coeff (a b c : K) (A B : K[X]) (n : Nat) :
    (oddPart a b c A B).coeff (n+1) =
      c*A.coeff (n+1)+a*B.coeff (n+1)+b*B.coeff n := by
  simp [oddPart, coeff_X_mul]

/-- Two high coefficients precisely characterize image membership. This is
symbolic in the degree cap: no 1024-entry expression is normalized. -/
theorem image_iff (a b c : K) (A B : K[X]) (n : Nat)
    (hA : A.natDegree ≤ n+1) (hB : B.natDegree ≤ n+1)
    (line : b ≠ 0 ∨ c ≠ 0) :
    ((evenPart a b c A B).natDegree ≤ n+1 ∧
      (oddPart a b c A B).natDegree ≤ n+1) ↔
    (B.coeff (n+1)=0 ∧ b*A.coeff (n+1)-c*B.coeff n=0) := by
  have Az : ∀ m, n+1 < m → A.coeff m=0 := natDegree_le_iff_coeff_eq_zero.mp hA
  have Bz : ∀ m, n+1 < m → B.coeff m=0 := natDegree_le_iff_coeff_eq_zero.mp hB
  constructor
  · rintro ⟨he,ho⟩
    have et := natDegree_le_iff_coeff_eq_zero.mp he (n+3) (by omega)
    have ot := natDegree_le_iff_coeff_eq_zero.mp ho (n+2) (by omega)
    rw [show n+3=(n+1)+2 by omega, even_coeff] at et
    rw [show n+2=(n+1)+1 by omega, odd_coeff] at ot
    have z2A := Az (n+2) (by omega)
    have z3A := Az (n+3) (by omega)
    have z2B := Bz (n+2) (by omega)
    have z3B := Bz (n+3) (by omega)
    have top : B.coeff (n+1)=0 := by
      rcases line with hb | hc
      · have v : b*B.coeff (n+1)=0 := by simpa [Nat.add_assoc, z2A,z2B] using ot
        exact (mul_eq_zero.mp v).resolve_left hb
      · have v : c*B.coeff (n+1)=0 := by
          simpa [Nat.add_assoc, z2A,z3A,z3B] using congrArg Neg.neg et
        exact (mul_eq_zero.mp v).resolve_left hc
    refine ⟨top,?_⟩
    have e := natDegree_le_iff_coeff_eq_zero.mp he (n+2) (by omega)
    rw [even_coeff] at e
    simpa [z2A,z2B,sub_eq_add_neg] using e
  · rintro ⟨top,relation⟩
    constructor
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
      rw [Nat.add_comm 2 r, even_coeff]
      have zA := Az (r+2) (by omega)
      have zB := Bz (r+2) (by omega)
      rw [zA,zB]
      by_cases eq : r=n
      · subst r; linear_combination relation
      · have za := Az (r+1) (by omega)
        have zb : B.coeff r=0 := by
          by_cases eq' : r=n+1
          · simpa [eq'] using top
          · exact Bz r (by omega)
        simp [za,zb]
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
      rw [Nat.add_comm 1 r, odd_coeff]
      have za := Az (r+1) (by omega)
      have zb := Bz (r+1) (by omega)
      have zb' : B.coeff r=0 := by
        by_cases eq : r=n+1
        · simpa [eq] using top
        · exact Bz r (by omega)
      simp [za,zb,zb']

/-- A low-degree affine interpolant changes neither image obstruction. -/
theorem add_interpolant_iff (E O IA IB : K[X]) (n : Nat)
    (ha : IA.natDegree ≤ n) (hb : IB.natDegree ≤ n) :
    ((E+IA).natDegree ≤ n ∧ (O+IB).natDegree ≤ n) ↔
      (E.natDegree ≤ n ∧ O.natDegree ≤ n) := by
  constructor
  · rintro ⟨he,ho⟩
    constructor
    · simpa using (natDegree_sub_le (E+IA) IA).trans (max_le he ha)
    · simpa using (natDegree_sub_le (O+IB) IB).trans (max_le ho hb)
  · rintro ⟨he,ho⟩
    exact ⟨(natDegree_add_le E IA).trans (max_le he ha),
      (natDegree_add_le O IB).trans (max_le ho hb)⟩

#print axioms chord_eval
#print axioms quotient_eq_reconstruction
#print axioms even_coeff
#print axioms odd_coeff
#print axioms image_iff
#print axioms add_interpolant_iff
end
end AspisV8.ChordPolynomialImage
