import R0.Fold
import Wide.EncoderLinearity

/-! The exact initial message space is the pair of polynomials of degree
at most 511, not the larger ambient GRS space. -/
set_option autoImplicit false
namespace AspisR0.PolynomialPair
open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV7ExactOneFoldDomains AspisCircleGroupOrder
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

theorem pair_complete (p0 p1 : K[X]) (h0 : p0.natDegree ≤ 511)
    (h1 : p1.natDegree ≤ 511) :
    ∃ q : InitialMessage K, initialP0 q = p0 ∧ initialP1 q = p1 := by
  obtain ⟨a, ha⟩ := naturalCoefficientPolynomial_complete (n := 512) (by decide) p0 h0
  obtain ⟨b, hb⟩ := naturalCoefficientPolynomial_complete (n := 512) (by decide) p1 h1
  let q : InitialMessage K := fun i =>
    if i.val % 2 = 0 then a ⟨i.val / 2, by omega⟩ else b ⟨i.val / 2, by omega⟩
  have even : evenCoefficients (n := 512) q = a := by
    funext i
    simp [evenCoefficients, q]
  have odd : oddCoefficients (n := 512) q = b := by
    funext i
    simp [oddCoefficients, q, Nat.add_div]
  exact ⟨q, by simpa only [initialP0, even] using ha,
    by simpa only [initialP1, odd] using hb⟩

def truncate (p : K[X]) : K[X] := monomialPolynomial (fun i : Fin 512 => p.coeff i)

theorem truncate_degree (p : K[X]) : (truncate p).natDegree ≤ 511 :=
  monomialPolynomial_natDegree_le (by decide) _

theorem truncate_eq (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · exact monomialPolynomial_coeff _ ⟨n, hn⟩
  · rw [truncate, monomialPolynomial_coeff_eq_zero_of_ge _ _ (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n)]

def lift (p0 p1 : K[X]) : InitialMessage K :=
  Classical.choose (pair_complete (truncate p0) (truncate p1)
    (truncate_degree p0) (truncate_degree p1))

theorem lift_spec (p0 p1 : K[X]) :
    initialP0 (lift p0 p1) = truncate p0 ∧ initialP1 (lift p0 p1) = truncate p1 :=
  Classical.choose_spec (pair_complete (truncate p0) (truncate p1)
    (truncate_degree p0) (truncate_degree p1))

theorem lift_bounded (p0 p1 : K[X]) (h0 : p0.natDegree ≤ 511)
    (h1 : p1.natDegree ≤ 511) :
    initialP0 (lift p0 p1) = p0 ∧ initialP1 (lift p0 p1) = p1 := by
  simpa only [truncate_eq p0 h0, truncate_eq p1 h1] using lift_spec p0 p1

def naturalLinear {n : Nat} (hn : 0 < n) : (Fin n → K) →ₗ[K] K[X] where
  toFun := naturalCoefficientPolynomial
  map_add' a b := by
    rw [naturalCoefficientPolynomial_eq_basisSum hn,
      naturalCoefficientPolynomial_eq_basisSum hn,
      naturalCoefficientPolynomial_eq_basisSum hn]
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    rw [naturalCoefficientPolynomial_eq_basisSum hn,
      naturalCoefficientPolynomial_eq_basisSum hn]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, smul_eq_C_mul,
      Finset.mul_sum, mul_assoc, RingHom.id_apply]

@[simp] theorem naturalLinear_apply {n : Nat} (hn : 0 < n) (a : Fin n → K) :
    naturalLinear hn a = naturalCoefficientPolynomial a := rfl

def p0Linear : InitialMessage K →ₗ[K] K[X] :=
  (naturalLinear (n := 512) (by decide)).comp (LinearMap.funLeft K K fun i : Fin 512 => ⟨2*i.val, by omega⟩)

def p1Linear : InitialMessage K →ₗ[K] K[X] :=
  (naturalLinear (n := 512) (by decide)).comp (LinearMap.funLeft K K fun i : Fin 512 => ⟨2*i.val+1, by omega⟩)

@[simp] theorem p0Linear_apply (q : InitialMessage K) : p0Linear q = initialP0 q := by
  simp only [p0Linear, LinearMap.comp_apply, naturalLinear_apply, initialP0]
  exact congrArg naturalCoefficientPolynomial (show _ = evenCoefficients (n := 512) q from funext fun i => rfl)
@[simp] theorem p1Linear_apply (q : InitialMessage K) : p1Linear q = initialP1 q := by
  simp only [p1Linear, LinearMap.comp_apply, naturalLinear_apply, initialP1]
  exact congrArg naturalCoefficientPolynomial (show _ = oddCoefficients (n := 512) q from funext fun i => rfl)

@[simp] theorem p0_add (q r : InitialMessage K) : initialP0 (q+r) = initialP0 q + initialP0 r := by
  simpa only [p0Linear_apply] using (p0Linear (K := K)).map_add q r
@[simp] theorem p1_add (q r : InitialMessage K) : initialP1 (q+r) = initialP1 q + initialP1 r := by
  simpa only [p1Linear_apply] using (p1Linear (K := K)).map_add q r
@[simp] theorem p0_smul (a : K) (q : InitialMessage K) : initialP0 (a • q) = a • initialP0 q := by
  simpa only [p0Linear_apply, RingHom.id_apply] using (p0Linear (K := K)).map_smul a q
@[simp] theorem p1_smul (a : K) (q : InitialMessage K) : initialP1 (a • q) = a • initialP1 q := by
  simpa only [p1Linear_apply, RingHom.id_apply] using (p1Linear (K := K)).map_smul a q

theorem truncate_add (p q : K[X]) : truncate (p+q) = truncate p + truncate q := by
  simp [truncate, monomialPolynomial, coeff_add, add_mul, Finset.sum_add_distrib]
theorem truncate_smul (a : K) (p : K[X]) : truncate (a • p) = a • truncate p := by
  simp [truncate, monomialPolynomial, smul_eq_C_mul, Finset.mul_sum, mul_assoc]

def liftLinear : (K[X] × K[X]) →ₗ[K] InitialMessage K where
  toFun p := lift p.1 p.2
  map_add' p q := by
    apply exactInitialPolynomialPair_injective
    apply Prod.ext
    · dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [(lift_spec _ _).1, p0_add,
        (lift_spec _ _).1, (lift_spec _ _).1]
      exact truncate_add _ _
    · dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [(lift_spec _ _).2, p1_add,
        (lift_spec _ _).2, (lift_spec _ _).2]
      exact truncate_add _ _
  map_smul' a p := by
    apply exactInitialPolynomialPair_injective
    apply Prod.ext
    · dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [(lift_spec _ _).1, p0_smul, (lift_spec _ _).1]
      exact truncate_smul _ _
    · dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [(lift_spec _ _).2, p1_smul, (lift_spec _ _).2]
      exact truncate_smul _ _

@[simp] theorem liftLinear_apply (p : K[X] × K[X]) : liftLinear p = lift p.1 p.2 := by
  simp only [liftLinear, LinearMap.coe_mk, AddHom.coe_mk]

theorem circleX_injective : Function.Injective (exactCircleX (K := K)) := by
  intro u v h
  apply storedFirstLineX18_injective
  apply FaithfulSMul.algebraMap_injective (ZMod P) K
  rw [storedFirstLineX18_eq_doubled_algebraMap, storedFirstLineX18_eq_doubled_algebraMap]
  exact congrArg (fun x => AspisCircleTensorBinding.doubledFactor x 1) h

theorem polynomial_eq_of_fibres (p q : K[X]) (hp : p.natDegree ≤ 513)
    (hq : q.natDegree ≤ 513)
    (h : ∀ u, p.eval (exactCircleX u) = q.eval (exactCircleX u)) : p = q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q circleX_injective h
  simp only [Fintype.card_fin]
  omega

#print axioms pair_complete
#print axioms liftLinear
#print axioms polynomial_eq_of_fibres
end
end AspisR0.PolynomialPair
