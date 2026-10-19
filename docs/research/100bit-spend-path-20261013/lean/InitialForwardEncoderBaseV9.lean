import WideExactNaturalBasisComputableV16
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5FriCircleEncoderDistance
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl

set_option autoImplicit false
namespace AspisWide.InitialForwardEncoderBaseV9

open CompPoly Polynomial
open AspisWide.NaturalBasisComputable
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisCircleTensorBinding

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]

def evenV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val, by omega⟩
def oddV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val + 1, by omega⟩

def encodeBasis : (n : Nat) → (Fin (n + 1) → K) → CPolynomial K
  | 0, c => CPolynomial.C (c 0) * cNaturalLinePoly (K := K) 0
  | n + 1, c =>
      encodeBasis n (fun i => c i.castSucc) +
        CPolynomial.C (c (Fin.last (n + 1))) * cNaturalLinePoly (K := K) (n + 1)

theorem encodeBasis_toPoly_basisSum : ∀ n (c : Fin (n + 1) → K),
    (encodeBasis (K := K) n c).toPoly =
      ∑ i : Fin (n + 1), C (c i) * naturalLinePoly K i.val := by
  intro n
  induction n with
  | zero =>
      intro c
      rw [encodeBasis, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
        cNaturalLinePoly_toPoly]
      simp [AspisCircleTensorBinding.naturalLinePoly]
  | succ n ih =>
      intro c
      rw [encodeBasis, CPolynomial.toPoly_add, ih,
        CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
        cNaturalLinePoly_toPoly]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp [AspisCircleTensorBinding.naturalLinePoly]

theorem encodeBasis_toPoly_initial (c : Fin 512 → K) :
    (encodeBasis (K := K) 511 c).toPoly = naturalCoefficientPolynomial c := by
  rw [encodeBasis_toPoly_basisSum]
  exact (naturalCoefficientPolynomial_eq_basisSum (K := K) (n := 512)
    (by omega) c).symm

theorem evenV_initial (m : Fin 1024 → K) :
    initialP0 m = naturalCoefficientPolynomial (evenV m) := rfl

theorem oddV_initial (m : Fin 1024 → K) :
    initialP1 m = naturalCoefficientPolynomial (oddV m) := rfl

def fractionalLiftC (d : Nat) (p : CPolynomial K) : CPolynomial K :=
  ∑ i ∈ Finset.range (d + 1),
    CPolynomial.C (p.coeff i) * (1 - CPolynomial.X) ^ i *
      (1 + CPolynomial.X) ^ (d - i)

theorem fractionalLiftC_toPoly (d : Nat) (p : CPolynomial K) :
    (fractionalLiftC d p).toPoly = fractionalLift d p.toPoly := by
  have hcoeff : ∀ i, p.coeff i = p.toPoly.coeff i := fun i =>
    CPolynomial.coeff_toPoly p i
  simp [fractionalLiftC, fractionalLift, CPolynomial.toPoly_sum,
    CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.toPoly_sub,
    CPolynomial.toPoly_add, CPolynomial.C_toPoly, CPolynomial.X_toPoly,
    CPolynomial.toPoly_one, hcoeff]

def scalarC : K →+* CPolynomial K where
  toFun := CPolynomial.C
  map_one' := by
    apply CPolynomial.ringEquiv.injective
    change (CPolynomial.C 1).toPoly = (1 : CPolynomial K).toPoly
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
  map_mul' a b := by
    apply CPolynomial.ringEquiv.injective
    change (CPolynomial.C (a * b)).toPoly =
      (CPolynomial.C a * CPolynomial.C b).toPoly
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_mul]
  map_zero' := by
    apply CPolynomial.ringEquiv.injective
    change (CPolynomial.C 0).toPoly = (0 : CPolynomial K).toPoly
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_zero]
  map_add' a b := by
    apply CPolynomial.ringEquiv.injective
    change (CPolynomial.C (a + b)).toPoly =
      (CPolynomial.C a + CPolynomial.C b).toPoly
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_add]

def expandTwoC (p : CPolynomial K) : CPolynomial K :=
  p.eval₂ scalarC (CPolynomial.X ^ 2)

theorem expandTwoC_toPoly (p : CPolynomial K) :
    (expandTwoC p).toPoly = Polynomial.expand K 2 p.toPoly := by
  rw [expandTwoC, CPolynomial.eval₂_eq_sum_support, CPolynomial.toPoly_sum,
    Polynomial.coe_expand, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  have hcoeff : ∀ j, p.coeff j = p.toPoly.coeff j := fun j =>
    CPolynomial.coeff_toPoly p j
  have hterm (j : Nat) :
      (scalarC (p.coeff j) * (CPolynomial.X ^ 2) ^ j).toPoly =
        Polynomial.C (p.toPoly.coeff j) * Polynomial.X ^ (2 * j) := by
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    simp [scalarC, CPolynomial.C_toPoly, hcoeff, pow_mul]
  rw [CPolynomial.support_toPoly p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hterm]
  simp [pow_mul]

def encodeInitialC (m : Fin 1024 → K) : CPolynomial K :=
  expandTwoC (fractionalLiftC 512 (encodeBasis (K := K) 511 (evenV m))) +
    (CPolynomial.C (2 : K) * CPolynomial.X) *
      expandTwoC (fractionalLiftC 511 (encodeBasis (K := K) 511 (oddV m)))

theorem encodeInitialC_toPoly (m : Fin 1024 → K) :
    (encodeInitialC m).toPoly = circleNumerator (initialP0 m) (initialP1 m) := by
  rw [encodeInitialC, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.X_toPoly,
    expandTwoC_toPoly, expandTwoC_toPoly,
    fractionalLiftC_toPoly, fractionalLiftC_toPoly,
    encodeBasis_toPoly_initial, encodeBasis_toPoly_initial,
    evenV_initial, oddV_initial]
  rw [circleNumerator, mobiusLift_eq_expand, mobiusLift_eq_expand]

#print axioms encodeBasis_toPoly_initial
#print axioms fractionalLiftC_toPoly
#print axioms expandTwoC_toPoly
#print axioms encodeInitialC_toPoly

end AspisWide.InitialForwardEncoderBaseV9
