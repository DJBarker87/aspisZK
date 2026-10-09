import ChordRationalDivisibility

/-! Four exact degree-bounded finals bound the SAME polynomial quotient
constructed by divisibility. No degree or leading-coefficient assumption is
made on the nonzero norm: use interpolation in the degree-bounded submodule,
not subtraction of a presumed norm degree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalQuotientDegree
open Polynomial AspisV8.ChordRationalAlgebra AspisV8.ChordRationalDegree
open AspisV8.ChordRationalDivisibility
noncomputable section
variable {K : Type*} [Field K]

theorem reconstructed_cleared_product (a b c : K) (u q : Fin 4 → K[X])
    (reconstruction : u=product radialS radialT q (line (C a) (C b) (C c))) :
    product radialS radialT u (clearedAdjugate a b c)=
      (fun j=>clearedNorm a b c*q j) := by
  rw [reconstruction,product_associative]
  change product radialS radialT q
      (product radialS radialT (line (C a) (C b) (C c))
        (adjugate (C a) (C b) (C c) radialS radialT))=_
  rw [line_adjugate,product_scalar_right]
  rfl

theorem folded_numerator_scalar (alpha : K) (N : K[X]) (q : Fin 4 → K[X]) :
    foldedNumerator alpha (fun j=>N*q j)=N*foldedNumerator alpha q := by
  simp only [foldedNumerator]
  ring

/-- Full POLYNOMIAL discrepancy equality is required, not equality at one
radial/query position. The final may depend on this alpha and prior challenges. -/
theorem exact_final_is_folded_quotient (a b c alpha : K) (u q : Fin 4 → K[X])
    (final : K[X]) (normNonzero : clearedNorm a b c≠0)
    (reconstruction : u=product radialS radialT q (line (C a) (C b) (C c)))
    (exactAt : clearedDiscrepancy a b c alpha u final=0) :
    foldedNumerator alpha q=final := by
  have equal := sub_eq_zero.mp exactAt
  change foldedNumerator alpha (product radialS radialT u (clearedAdjugate a b c))=
    clearedNorm a b c*final at equal
  rw [reconstructed_cleared_product a b c u q reconstruction,folded_numerator_scalar] at equal
  exact mul_left_cancel₀ normNonzero equal

/-- The existing degreeLE submodule includes zero correctly. The four finals
are independently supplied polynomials; none is frozen before its alpha here. -/
theorem four_bounded_folds_bound_coefficients (q : Fin 4 → K[X])
    (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X]) (d : Nat)
    (exactAt : ∀ i : Fin 4,foldedNumerator (nodes i) q=finals i)
    (bounded : ∀ i : Fin 4,(finals i).natDegree≤d) :
    ∀ j : Fin 4,(q j).natDegree≤d := by
  have inside (i : Fin 4) :
      q 0+(nodes i) • q 1+(nodes i)^2 • q 2+(nodes i)^3 • q 3∈
        Polynomial.degreeLE K (d:WithBot Nat) := by
    rw [←folded_numerator_is_cubic,exactAt i,Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_of_natDegree_le (bounded i)
  have recovered:=AspisV8.FourPointSubmodule.literal_cubic_four_points
    (Polynomial.degreeLE K (d:WithBot Nat)) q nodes distinct inside
  intro j
  exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp (recovered j))

/-- Construct one polynomial quotient from the four exact cleared equations,
then bind every supplied final and recover the degree of every component of
that SAME quotient. No independent q or expected anchor is supplied. -/
theorem four_exact_bounded_finals_construct_quotient (a b c : K)
    (u : Fin 4 → K[X]) (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X]) (d : Nat) (normNonzero : clearedNorm a b c≠0)
    (exactAt : ∀ i : Fin 4,clearedDiscrepancy a b c (nodes i) u (finals i)=0)
    (bounded : ∀ i : Fin 4,(finals i).natDegree≤d) :
    ∃ q : Fin 4 → K[X],
      u=product radialS radialT q (line (C a) (C b) (C c)) ∧
      (∀ j : Fin 4,(q j).natDegree≤d) ∧
      (∀ i : Fin 4,foldedNumerator (nodes i) q=finals i) := by
  obtain ⟨q,reconstruction⟩:=four_exact_folds_construct_polynomial_quotient a b c u nodes
    distinct finals normNonzero exactAt
  have folded (i : Fin 4) : foldedNumerator (nodes i) q=finals i :=
    exact_final_is_folded_quotient a b c (nodes i) u q (finals i) normNonzero
      reconstruction (exactAt i)
  exact ⟨q,reconstruction,
    four_bounded_folds_bound_coefficients q nodes distinct finals d folded bounded,folded⟩

theorem four_exact_final256_construct_quotient (a b c : K)
    (u : Fin 4 → K[X]) (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X]) (normNonzero : clearedNorm a b c≠0)
    (exactAt : ∀ i : Fin 4,clearedDiscrepancy a b c (nodes i) u (finals i)=0)
    (bounded : ∀ i : Fin 4,(finals i).natDegree≤255) :
    ∃ q : Fin 4 → K[X],
      u=product radialS radialT q (line (C a) (C b) (C c)) ∧
      (∀ j : Fin 4,(q j).natDegree≤255) ∧
      (∀ i : Fin 4,foldedNumerator (nodes i) q=finals i) :=
  four_exact_bounded_finals_construct_quotient a b c u nodes distinct finals 255
    normNonzero exactAt bounded

#print axioms reconstructed_cleared_product
#print axioms folded_numerator_scalar
#print axioms exact_final_is_folded_quotient
#print axioms four_bounded_folds_bound_coefficients
#print axioms four_exact_bounded_finals_construct_quotient
#print axioms four_exact_final256_construct_quotient
end
end AspisV8.ChordRationalQuotientDegree
