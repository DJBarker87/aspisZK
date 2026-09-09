import ChordRationalDegree
import FourPointSubmodule

/-! Exact cleared-fold equalities at four distinct challenges force a
polynomial quotient representation. Finals may differ between challenges.
This proves neither a degree cap for the reconstructed quotient nor image/
original-code membership, and never assumes an arbitrary received oracle has
polynomial components. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000
namespace AspisV8.ChordRationalDivisibility
open Polynomial AspisV8.ChordRationalAlgebra AspisV8.ChordRationalDegree
noncomputable section

section Product
variable {R : Type*} [CommRing R]

theorem product_commutative (s t : R) (u v : Fin 4 → R) :
    product s t u v=product s t v u := by
  funext j
  fin_cases j <;> simp [product] <;> ring

theorem product_associative (s t : R) (u v w : Fin 4 → R) :
    product s t (product s t u v) w=product s t u (product s t v w) := by
  funext j
  fin_cases j <;> simp [product] <;> ring

theorem product_scalar_left (s t scalar : R) (u v : Fin 4 → R) :
    product s t (fun j=>scalar*u j) v=(fun j=>scalar*product s t u v j) := by
  funext j
  fin_cases j <;> simp [product] <;> ring

theorem product_scalar_right (s t scalar : R) (u : Fin 4 → R) :
    product s t u ![scalar,0,0,0]=(fun j=>scalar*u j) := by
  funext j
  fin_cases j <;> simp [product] <;> ring

/-- The explicit adjugate is a two-sided inverse up to its norm in the
four-component commutative algebra; no fibre evaluation injectivity is used. -/
theorem cleared_then_line (a b c s t : R) (u : Fin 4 → R) :
    product s t (product s t u (adjugate a b c s t)) (line a b c)=
      (fun j=>norm a b c s t*u j) := by
  rw [product_associative,
    product_commutative s t (adjugate a b c s t) (line a b c),
    line_adjugate,product_scalar_right]
end Product

variable {K : Type*} [Field K]

/-- The actual principal ideal, viewed as a K-submodule rather than a
K[X]-submodule so four FIELD challenges can use interpolation. -/
def normMultiples (N : K[X]) : Submodule K K[X] :=
  (Ideal.span ({N}:Set K[X])).restrictScalars K

theorem mem_normMultiples (N p : K[X]) : p∈normMultiples N ↔ N∣p := by
  change p∈Ideal.span ({N}:Set K[X]) ↔ N∣p
  exact Ideal.mem_span_singleton

theorem folded_numerator_is_cubic (alpha : K) (w : Fin 4 → K[X]) :
    foldedNumerator alpha w=w 0+alpha • w 1+alpha^2 • w 2+alpha^3 • w 3 := by
  simp only [foldedNumerator,Polynomial.smul_eq_C_mul,map_pow]

/-- Each exact discrepancy supplies a possibly different final polynomial.
Four such exact relations suffice; no degree condition or fixed-final premise
is smuggled into the interpolation step. -/
theorem four_exact_discrepancies_divide (a b c : K) (u : Fin 4 → K[X])
    (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X])
    (exactAt : ∀ i : Fin 4,clearedDiscrepancy a b c (nodes i) u (finals i)=0) :
    ∀ j : Fin 4,clearedNorm a b c∣
      product radialS radialT u (clearedAdjugate a b c) j := by
  let w:=product radialS radialT u (clearedAdjugate a b c)
  have inside (i : Fin 4) :
      w 0+(nodes i) • w 1+(nodes i)^2 • w 2+(nodes i)^3 • w 3∈
        normMultiples (clearedNorm a b c) := by
    rw [←folded_numerator_is_cubic,mem_normMultiples]
    refine ⟨finals i,?_⟩
    exact sub_eq_zero.mp (exactAt i)
  have recovered:=AspisV8.FourPointSubmodule.literal_cubic_four_points
    (normMultiples (clearedNorm a b c)) w nodes distinct inside
  intro j
  exact (mem_normMultiples _ _).mp (recovered j)

/-- Divisibility itself constructs q. Nonzero norm permits cancellation in
K[X]; q's degree/image and source encoding are NOT conclusions here. -/
theorem divisible_components_reconstruct (a b c : K) (u : Fin 4 → K[X])
    (normNonzero : clearedNorm a b c≠0)
    (divisible : ∀ j : Fin 4,clearedNorm a b c∣
      product radialS radialT u (clearedAdjugate a b c) j) :
    ∃ q : Fin 4 → K[X],u=product radialS radialT q (line (C a) (C b) (C c)) := by
  choose q hq using divisible
  have components : product radialS radialT u (clearedAdjugate a b c)=
      (fun j=>clearedNorm a b c*q j) := funext hq
  have cancelled:=cleared_then_line (C a) (C b) (C c) radialS radialT u
  change product radialS radialT (product radialS radialT u (clearedAdjugate a b c))
      (line (C a) (C b) (C c))=(fun j=>clearedNorm a b c*u j) at cancelled
  rw [components,product_scalar_left] at cancelled
  refine ⟨q,?_⟩
  funext j
  exact (mul_left_cancel₀ normNonzero (congrFun cancelled j)).symm

theorem four_exact_folds_construct_polynomial_quotient (a b c : K)
    (u : Fin 4 → K[X]) (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X]) (normNonzero : clearedNorm a b c≠0)
    (exactAt : ∀ i : Fin 4,clearedDiscrepancy a b c (nodes i) u (finals i)=0) :
    ∃ q : Fin 4 → K[X],u=product radialS radialT q (line (C a) (C b) (C c)) :=
  divisible_components_reconstruct a b c u normNonzero
    (four_exact_discrepancies_divide a b c u nodes distinct finals exactAt)

#print axioms product_commutative
#print axioms product_associative
#print axioms product_scalar_left
#print axioms product_scalar_right
#print axioms cleared_then_line
#print axioms mem_normMultiples
#print axioms folded_numerator_is_cubic
#print axioms four_exact_discrepancies_divide
#print axioms divisible_components_reconstruct
#print axioms four_exact_folds_construct_polynomial_quotient
end
end AspisV8.ChordRationalDivisibility
