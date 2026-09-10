import QuadraticSpecializationKernel
import QuadraticSpecializationBasis
import QuadraticSpecializationCount

/-!
Actual Sylvester-matrix consumer. The independent vectors and invertible
constant basis change are constructed, not assumed. The final count still
requires a nonzero resultant and an actual square specialization at every
counted challenge. Primitive decomposition / source applicability is not
asserted by this leaf.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationSylvester
noncomputable section
open Module Polynomial
open scoped Matrix
open QuadraticSpecializationKernel

abbrev Blocks (K : Type*) [Field K] (m : Nat) :=
  Polynomial.degreeLT K (2 * m) × Polynomial.degreeLT K (2 * m - 1)

private theorem input_natDegree_lt
    {K : Type*} [Field K] (m : Nat) (positive : 0 < m)
    (s : Polynomial.degreeLT K m) : (s : K[X]).natDegree < m := by
  by_cases zero : (s : K[X]) = 0
  · simpa only [zero, Polynomial.natDegree_zero] using positive
  · exact (Polynomial.natDegree_lt_iff_degree_lt zero).mpr
      (Polynomial.mem_degreeLT.mp s.property)

/-- The actual bounded kernel map, linear on the complete m-dimensional
input polynomial space rather than only on selected monomials. -/
def boundedKernelMap
    {K : Type*} [Field K] (V : K[X]) (m : Nat)
    (positive : 0 < m) (degree : V.natDegree ≤ m) :
    Polynomial.degreeLT K m →ₗ[K] Blocks K m where
  toFun s :=
    (⟨(squareKernelPair V s).1, Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt (Nat.cast_lt.mpr
          (square_kernel_pair_degree V s m positive degree
            (input_natDegree_lt m positive s)).1))⟩,
     ⟨(squareKernelPair V s).2, Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt (Nat.cast_lt.mpr
          (square_kernel_pair_degree V s m positive degree
            (input_natDegree_lt m positive s)).2))⟩)
  map_add' s t := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (square_kernel_pair_add V s t)
    · exact congrArg Prod.snd (square_kernel_pair_add V s t)
  map_smul' c s := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (square_kernel_pair_smul V s c)
    · exact congrArg Prod.snd (square_kernel_pair_smul V s c)

theorem bounded_kernel_injective
    {K : Type*} [Field K] (V : K[X]) (m : Nat)
    (positive : 0 < m) (degree : V.natDegree ≤ m) (nonzero : V ≠ 0) :
    Function.Injective (boundedKernelMap V m positive degree) := by
  intro s t equal
  apply Subtype.ext
  apply square_kernel_pair_injective V nonzero
  exact congrArg (fun pair : Blocks K m =>
    ((pair.1 : K[X]), (pair.2 : K[X]))) equal

theorem bounded_kernel_zero
    {K : Type*} [Field K] (c : K) (V : K[X]) (m : Nat)
    (positive : 0 < m) (degree : V.natDegree ≤ m)
    (s : Polynomial.degreeLT K m) :
    Polynomial.sylvesterMap (Polynomial.C c * V ^ 2)
      (Polynomial.C c * V ^ 2).derivative
      (square_degree_bounds c V m degree).1
      (square_degree_bounds c V m degree).2
      (boundedKernelMap V m positive degree s) = 0 := by
  exact actual_sylvester_map_zero c V s m positive degree
    (input_natDegree_lt m positive s)

/-- The monomial basis is transported through the proved injective bounded
map and the literal source coefficient basis. The resulting family lies in
the kernel of the actual square-polynomial Sylvester matrix. -/
theorem exists_actual_independent_kernel
    {K : Type*} [Field K] (c : K) (V : K[X]) (m : Nat)
    (positive : 0 < m) (degree : V.natDegree ≤ m) (nonzero : V ≠ 0) :
    ∃ v : Fin m → Fin (2 * m + (2 * m - 1)) → K,
      LinearIndependent K v ∧ ∀ j,
        (Polynomial.C c * V ^ 2).sylvester
          (Polynomial.C c * V ^ 2).derivative (2 * m) (2 * m - 1) *ᵥ v j = 0 := by
  classical
  let inputBasis := Polynomial.degreeLT.basis K m
  let domainBasis := Polynomial.degreeLT.basisProd K (2 * m) (2 * m - 1)
  let outputBasis := Polynomial.degreeLT.basis K (2 * m + (2 * m - 1))
  let coefficientMap := domainBasis.equivFun.toLinearMap.comp
    (boundedKernelMap V m positive degree)
  have coefficientInjective : Function.Injective coefficientMap :=
    domainBasis.equivFun.injective.comp
      (bounded_kernel_injective V m positive degree nonzero)
  let v := coefficientMap ∘ inputBasis
  have independent : LinearIndependent K v := inputBasis.linearIndependent.map'
    coefficientMap (LinearMap.ker_eq_bot.mpr coefficientInjective)
  refine ⟨v, independent, ?_⟩
  intro j
  let f := Polynomial.sylvesterMap (Polynomial.C c * V ^ 2)
    (Polynomial.C c * V ^ 2).derivative
    (square_degree_bounds c V m degree).1
    (square_degree_bounds c V m degree).2
  have matrix : f.toMatrix domainBasis outputBasis =
      (Polynomial.C c * V ^ 2).sylvester
        (Polynomial.C c * V ^ 2).derivative (2 * m) (2 * m - 1) := by
    exact Polynomial.toMatrix_sylvesterMap' _ _ _ _
  have coefficientZero := f.toMatrix_mulVec_repr domainBasis outputBasis
    (boundedKernelMap V m positive degree (inputBasis j))
  rw [matrix, bounded_kernel_zero] at coefficientZero
  have vectorRepresentation : v j =
      domainBasis.repr (boundedKernelMap V m positive degree (inputBasis j)) := by
    change domainBasis.equivFun
      (boundedKernelMap V m positive degree (inputBasis j)) = _
    exact domainBasis.equivFun_apply _
  rw [vectorRepresentation]
  simpa only [map_zero, Finsupp.coe_zero] using coefficientZero

/-- For the actual fixed-size Sylvester determinant, every nonzero square
specialization supplies m-fold divisibility. All coefficient/index and
kernel/basis implications are derived here; there is no supplied corank or
determinant-multiplicity premise. -/
theorem square_specialization_multiplicity
    {K : Type*} [Field K] (R : Polynomial K[X]) (gamma c : K)
    (V : K[X]) (m : Nat) (positive : 0 < m)
    (degree : V.natDegree ≤ m) (nonzero : V ≠ 0)
    (square : R.map (Polynomial.evalRingHom gamma) = Polynomial.C c * V ^ 2) :
    (Polynomial.X - Polynomial.C gamma) ^ m ∣
      R.resultant R.derivative (2 * m) (2 * m - 1) := by
  classical
  obtain ⟨v, independent, kernel⟩ :=
    exists_actual_independent_kernel c V m positive degree nonzero
  let M := R.sylvester R.derivative (2 * m) (2 * m - 1)
  have specialization : (Polynomial.evalRingHom gamma).mapMatrix M =
      (Polynomial.C c * V ^ 2).sylvester
        (Polynomial.C c * V ^ 2).derivative (2 * m) (2 * m - 1) := by
    rw [← Polynomial.sylvester_map_map, ← Polynomial.derivative_map, square]
  have actualKernel : ∀ j, (Polynomial.evalRingHom gamma).mapMatrix M *ᵥ v j = 0 := by
    rw [specialization]
    exact kernel
  have multiplicity := QuadraticSpecializationBasis.independent_kernel_pow_dvd_det
    M gamma v independent actualKernel
  simpa only [Fintype.card_fin, Polynomial.resultant] using multiplicity

/-- Quantitative consumer: the exact square-specialization hypothesis now
replaces the former caller-supplied multiplicity condition. Nonzero
resultant and coefficient-degree bounds still require their real proofs. -/
theorem square_specializations_card_le
    {K : Type*} [Field K] (R : Polynomial K[X]) (m delta : Nat)
    (positive : 0 < m)
    (coefficients : ∀ i, (R.coeff i).natDegree ≤ delta)
    (nonzero : R.resultant R.derivative (2 * m) (2 * m - 1) ≠ 0)
    (G : Finset K)
    (squares : ∀ gamma ∈ G, ∃ c V,
      V ≠ 0 ∧ V.natDegree ≤ m ∧
        R.map (Polynomial.evalRingHom gamma) = Polynomial.C c * V ^ 2) :
    G.card ≤ 4 * delta := by
  apply QuadraticSpecializationCount.square_specializations_card_le
    R m delta positive coefficients nonzero G
  intro gamma member
  obtain ⟨c, V, vNonzero, vDegree, square⟩ := squares gamma member
  exact square_specialization_multiplicity R gamma c V m positive vDegree vNonzero square

#print axioms bounded_kernel_injective
#print axioms bounded_kernel_zero
#print axioms exists_actual_independent_kernel
#print axioms square_specialization_multiplicity
#print axioms square_specializations_card_le

end
end AspisV8.QuadraticSpecializationSylvester
