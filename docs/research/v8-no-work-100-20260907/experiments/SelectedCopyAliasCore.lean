import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Narrow symbolic port of the generic polynomial lemmas in
V7DeployedCopyLogUpCollisionBounds. No 183-link registry, old error inventory,
or implication from sampled acceptance is imported. Both error polynomials
are explicit; field characteristic and poles remain stated hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedCopyAliasCore
noncomputable section
open Polynomial

/-- Below the characteristic, a zero derivative forces a polynomial to be
constant.  This is the exact positive-characteristic guard needed by the
fixed-size LogUp argument. -/
theorem natDegree_eq_zero_of_derivative_eq_zero_of_lt_char
    {K : Type*} [Field K]
    {f : K[X]} (derivativeZero : f.derivative = 0)
    (smallNatCasts : ∀ n : Nat, 0 < n → n ≤ f.natDegree → (n : K) ≠ 0) :
    f.natDegree = 0 := by
  by_contra degreeNonzero
  have degreePositive : 0 < f.natDegree := Nat.pos_of_ne_zero degreeNonzero
  have coefficientZero := congrArg
    (fun polynomial : K[X] => polynomial.coeff (f.natDegree - 1))
    derivativeZero
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at coefficientZero
  have predecessor : f.natDegree - 1 + 1 = f.natDegree := by omega
  rw [predecessor] at coefficientZero
  have castPredecessor :
      ((f.natDegree - 1 : Nat) : K) + 1 = (f.natDegree : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun value : Nat => (value : K)) predecessor
  rw [castPredecessor] at coefficientZero
  change f.leadingCoeff * (f.natDegree : K) = 0 at coefficientZero
  have castNonzero : (f.natDegree : K) ≠ 0 :=
    smallNatCasts f.natDegree degreePositive le_rfl
  have polynomialNonzero : f ≠ 0 := by
    intro polynomialZero
    apply degreeNonzero
    rw [polynomialZero]
    rfl
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
    polynomialNonzero) castNonzero)
    coefficientZero

/-- Two distinct monic polynomials of the same degree below the
characteristic have a nonzero Wronskian.  The proof cancels their gcd and uses
the kernel characterization of a coprime zero-Wronskian pair. -/
theorem wronskian_ne_zero_of_distinct_monic_same_small_degree
    {K : Type*} [Field K] [DecidableEq K]
    {p q : K[X]} (pMonic : p.Monic) (qMonic : q.Monic)
    (sameDegree : p.natDegree = q.natDegree)
    (smallNatCasts : ∀ n : Nat, 0 < n → n ≤ p.natDegree → (n : K) ≠ 0)
    (different : p ≠ q) :
    p.wronskian q ≠ 0 := by
  intro wronskianZero
  let g : K[X] := GCDMonoid.gcd p q
  let a : K[X] := p / g
  let b : K[X] := q / g
  have pNonzero : p ≠ 0 := pMonic.ne_zero
  have qNonzero : q ≠ 0 := qMonic.ne_zero
  have gNonzero : g ≠ 0 := gcd_ne_zero_of_right qNonzero
  have gp : g ∣ p := GCDMonoid.gcd_dvd_left p q
  have gq : g ∣ q := GCDMonoid.gcd_dvd_right p q
  have pFactor : g * a = p := EuclideanDomain.mul_div_cancel' gNonzero gp
  have qFactor : g * b = q := EuclideanDomain.mul_div_cancel' gNonzero gq
  have aNonzero : a ≠ 0 := left_div_gcd_ne_zero pNonzero
  have bNonzero : b ≠ 0 := right_div_gcd_ne_zero qNonzero
  have reducedCoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd qNonzero
  have reducedWronskianZero : a.wronskian b = 0 := by
    have factored : p.wronskian q = g ^ 2 * a.wronskian b := by
      rw [← pFactor, ← qFactor]
      simp only [Polynomial.wronskian, Polynomial.derivative_mul]
      ring
    rw [factored] at wronskianZero
    exact (mul_eq_zero.mp wronskianZero).resolve_left (pow_ne_zero 2 gNonzero)
  have derivativeZeros : a.derivative = 0 ∧ b.derivative = 0 :=
    reducedCoprime.wronskian_eq_zero_iff.mp reducedWronskianZero
  have aDvdP : a ∣ p := ⟨g, by simpa [mul_comm] using pFactor.symm⟩
  have bDvdQ : b ∣ q := ⟨g, by simpa [mul_comm] using qFactor.symm⟩
  have aDegreeBound : a.natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd aDvdP pNonzero
  have bDegreeBound : b.natDegree ≤ p.natDegree := by
    rw [sameDegree]
    exact Polynomial.natDegree_le_of_dvd bDvdQ qNonzero
  have aDegreeZero :=
    natDegree_eq_zero_of_derivative_eq_zero_of_lt_char derivativeZeros.1
      (fun n positive bounded =>
        smallNatCasts n positive (bounded.trans aDegreeBound))
  have bDegreeZero :=
    natDegree_eq_zero_of_derivative_eq_zero_of_lt_char derivativeZeros.2
      (fun n positive bounded =>
        smallNatCasts n positive (bounded.trans bDegreeBound))
  have aUnit : IsUnit a := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    rw [Polynomial.degree_eq_natDegree aNonzero, aDegreeZero]
    rfl
  have bUnit : IsUnit b := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    rw [Polynomial.degree_eq_natDegree bNonzero, bDegreeZero]
    rfl
  have pDvdQ : p ∣ q := by
    rw [← pFactor, ← qFactor]
    exact mul_dvd_mul_left g (aUnit.dvd)
  have qDvdP : q ∣ p := by
    rw [← pFactor, ← qFactor]
    exact mul_dvd_mul_left g (bUnit.dvd)
  exact different (Polynomial.eq_of_monic_of_associated pMonic qMonic
    (associated_of_dvd_dvd pDvdQ qDvdP))

/-! ## Characteristic polynomials for arbitrary finite multisets -/

noncomputable def multisetCharacteristicPolynomial
    {K : Type*} [CommRing K] (values : Multiset K) : K[X] :=
  (values.map fun value => X - C value).prod

@[simp] theorem multisetCharacteristicPolynomial_roots
    {K : Type*} [CommRing K] [IsDomain K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).roots = values := by
  exact Polynomial.roots_multiset_prod_X_sub_C values

theorem multisetCharacteristicPolynomial_monic
    {K : Type*} [CommRing K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C values

@[simp] theorem multisetCharacteristicPolynomial_natDegree
    {K : Type*} [CommRing K] [Nontrivial K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).natDegree = values.card := by
  exact Polynomial.natDegree_multiset_prod_X_sub_C_eq_card values

theorem multisetCharacteristicPolynomial_injective
    {K : Type*} [CommRing K] [IsDomain K] :
    Function.Injective (multisetCharacteristicPolynomial (K := K)) := by
  intro left right equal
  rw [← multisetCharacteristicPolynomial_roots left,
    ← multisetCharacteristicPolynomial_roots right, equal]

theorem multisetCharacteristicPolynomial_splits
    {K : Type*} [Field K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).Splits := by
  rw [Polynomial.splits_iff_card_roots,
    multisetCharacteristicPolynomial_roots,
    multisetCharacteristicPolynomial_natDegree]

theorem eval_multisetCharacteristicPolynomial_ne_zero
    {K : Type*} [Field K] (values : Multiset K) (challenge : K)
    (notPole : challenge ∉ values) :
    (multisetCharacteristicPolynomial values).eval challenge ≠ 0 := by
  rw [multisetCharacteristicPolynomial, Polynomial.eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply]
  apply Multiset.prod_ne_zero
  intro zeroMember
  simp only [Multiset.mem_map] at zeroMember
  obtain ⟨value, valueMember, factorZero⟩ := zeroMember
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at factorZero
  have challengeEqual : challenge = value := sub_eq_zero.mp factorZero
  exact notPole (challengeEqual.symm ▸ valueMember)

/-- Away from the explicitly listed poles, the characteristic polynomial's
logarithmic derivative is the exact multiset sum used by LogUp. -/
theorem eval_derivative_div_eval_multisetCharacteristicPolynomial
    {K : Type*} [Field K] (values : Multiset K) (challenge : K)
    (notPole : challenge ∉ values) :
    (multisetCharacteristicPolynomial values).derivative.eval challenge /
        (multisetCharacteristicPolynomial values).eval challenge =
      (values.map fun value => (challenge - value)⁻¹).sum := by
  have split := multisetCharacteristicPolynomial_splits values
  have nonzero :=
    eval_multisetCharacteristicPolynomial_ne_zero values challenge notPole
  simpa [multisetCharacteristicPolynomial_roots, one_div] using
    split.eval_derivative_div_eval_of_ne_zero nonzero

theorem map_multisetCharacteristicPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (values : Multiset R) :
    (multisetCharacteristicPolynomial values).map hom =
      multisetCharacteristicPolynomial (values.map hom) := by
  simp [multisetCharacteristicPolynomial, Polynomial.map_multiset_prod]

/-- Every coefficient of a characteristic polynomial built from degree-`d`
roots has degree at most `d * card`.  This is the non-factorial core of the
lambda analysis. -/
theorem multisetCharacteristicPolynomial_coeff_natDegree_le
    {K : Type*} [Field K] (values : Multiset K[X]) (degreeBound : Nat)
    (bounded : ∀ value ∈ values, value.natDegree ≤ degreeBound)
    (coefficient : Nat) :
    ((multisetCharacteristicPolynomial values).coeff coefficient).natDegree ≤
      degreeBound * values.card := by
  induction values using Multiset.induction_on generalizing coefficient with
  | empty =>
      rw [multisetCharacteristicPolynomial]
      simp only [Multiset.map_zero, Multiset.prod_zero]
      by_cases coefficientZero : coefficient = 0
      · subst coefficient
        simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        · rfl
        · simp
          omega
  | @cons value rest induction =>
      have valueBound : value.natDegree ≤ degreeBound :=
        bounded value (by simp)
      have restBound : ∀ other ∈ rest, other.natDegree ≤ degreeBound := by
        intro other member
        exact bounded other (Multiset.mem_cons_of_mem member)
      rw [multisetCharacteristicPolynomial, Multiset.map_cons,
        Multiset.prod_cons, Polynomial.coeff_mul]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro pair _
      refine Polynomial.natDegree_mul_le.trans ?_
      have factorBound :
          (((X - C value : K[X][X]).coeff pair.1).natDegree ≤
            degreeBound) := by
        rcases pair.1 with _ | index
        · simpa using valueBound
        · rcases index with _ | index
          · simp
          · rw [Polynomial.coeff_sub, Polynomial.coeff_X,
              Polynomial.coeff_C]
            simp
      have restCoefficientBound :
          ((multisetCharacteristicPolynomial rest).coeff pair.2).natDegree ≤
            degreeBound * rest.card :=
        induction restBound pair.2
      calc
        ((X - C value : K[X][X]).coeff pair.1).natDegree +
            ((multisetCharacteristicPolynomial rest).coeff pair.2).natDegree ≤
          degreeBound + degreeBound * rest.card :=
            Nat.add_le_add factorBound restCoefficientBound
        _ = degreeBound * (value ::ₘ rest).card := by
          simp
          ring



variable {K : Type*} [Field K]

def rationalBalance (producer consumer : Multiset K) (chi : K) : K :=
  (producer.map fun value => (chi-value)⁻¹).sum -
    (consumer.map fun value => (chi-value)⁻¹).sum

def chiError (producer consumer : Multiset K) : K[X] :=
  (multisetCharacteristicPolynomial producer).wronskian
    (multisetCharacteristicPolynomial consumer)

theorem chiError_eval_zero (producer consumer : Multiset K) (chi : K)
    (balance : rationalBalance producer consumer chi=0)
    (noProducerPole : chi∉producer) (noConsumerPole : chi∉consumer) :
    (chiError producer consumer).eval chi=0 := by
  let p := multisetCharacteristicPolynomial producer
  let q := multisetCharacteristicPolynomial consumer
  have pn : p.eval chi≠0 :=
    eval_multisetCharacteristicPolynomial_ne_zero producer chi noProducerPole
  have qn : q.eval chi≠0 :=
    eval_multisetCharacteristicPolynomial_ne_zero consumer chi noConsumerPole
  have same : p.derivative.eval chi/p.eval chi=q.derivative.eval chi/q.eval chi := by
    rw [eval_derivative_div_eval_multisetCharacteristicPolynomial producer chi noProducerPole,
      eval_derivative_div_eval_multisetCharacteristicPolynomial consumer chi noConsumerPole]
    exact sub_eq_zero.mp balance
  have cross := (div_eq_div_iff pn qn).mp same
  change (p.wronskian q).eval chi=0
  simp only [Polynomial.wronskian,Polynomial.eval_sub,Polynomial.eval_mul]
  rw [mul_comm (p.eval chi) (q.derivative.eval chi),cross,sub_self]

theorem chiError_nonzero (producer consumer : Multiset K)
    (sameCard : producer.card=consumer.card)
    (small : ∀ n : Nat,0<n → n≤producer.card → (n:K)≠0)
    (different : producer≠consumer) : chiError producer consumer≠0 := by
  classical
  apply wronskian_ne_zero_of_distinct_monic_same_small_degree
    (multisetCharacteristicPolynomial_monic producer)
    (multisetCharacteristicPolynomial_monic consumer)
  · simpa only [multisetCharacteristicPolynomial_natDegree] using sameCard
  · simpa only [multisetCharacteristicPolynomial_natDegree] using small
  · exact fun same => different (multisetCharacteristicPolynomial_injective same)

theorem chiError_degree (producer consumer : Multiset K)
    (nonzero : chiError producer consumer≠0) :
    (chiError producer consumer).natDegree<producer.card+consumer.card := by
  simpa only [chiError,multisetCharacteristicPolynomial_natDegree] using
    Polynomial.natDegree_wronskian_lt_add nonzero

/-- One sampled balance yields equality OR a root of this fixed polynomial.
It never yields an unproved polynomial identity. -/
theorem chi_root_or_equal (producer consumer : Multiset K) (chi : K)
    (sameCard : producer.card=consumer.card)
    (small : ∀ n : Nat,0<n → n≤producer.card → (n:K)≠0)
    (balance : rationalBalance producer consumer chi=0)
    (noProducerPole : chi∉producer) (noConsumerPole : chi∉consumer) :
    producer=consumer ∨
      chiError producer consumer≠0 ∧ (chiError producer consumer).eval chi=0 ∧
        (chiError producer consumer).natDegree<producer.card+consumer.card := by
  by_cases same : producer=consumer
  · exact Or.inl same
  · have nonzero := chiError_nonzero producer consumer sameCard small same
    exact Or.inr ⟨nonzero,chiError_eval_zero producer consumer chi balance
      noProducerPole noConsumerPole,chiError_degree producer consumer nonzero⟩

/-- Fixed before lambda. This is one coefficient witness, not a union over
all pairs of compressed tuples or an assumed permutation after lambda. -/
def lambdaError (producer consumer : Multiset K[X]) : K[X] :=
  (multisetCharacteristicPolynomial producer -
    multisetCharacteristicPolynomial consumer).leadingCoeff

theorem lambdaError_nonzero (producer consumer : Multiset K[X])
    (different : producer≠consumer) : lambdaError producer consumer≠0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro zero
  exact different (multisetCharacteristicPolynomial_injective (sub_eq_zero.mp zero))

theorem lambdaError_degree (producer consumer : Multiset K[X]) (d : Nat)
    (pb : ∀ p∈producer,p.natDegree≤d) (qb : ∀ q∈consumer,q.natDegree≤d) :
    (lambdaError producer consumer).natDegree≤d*max producer.card consumer.card := by
  unfold lambdaError Polynomial.leadingCoeff
  rw [Polynomial.coeff_sub]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (multisetCharacteristicPolynomial_coeff_natDegree_le producer d pb _).trans
      (Nat.mul_le_mul_left d (le_max_left _ _))
  · exact (multisetCharacteristicPolynomial_coeff_natDegree_le consumer d qb _).trans
      (Nat.mul_le_mul_left d (le_max_right _ _))

theorem lambdaError_eval_zero (producer consumer : Multiset K[X]) (lambda : K)
    (equal : producer.map (Polynomial.evalRingHom lambda)=
      consumer.map (Polynomial.evalRingHom lambda)) :
    (lambdaError producer consumer).eval lambda=0 := by
  let difference := multisetCharacteristicPolynomial producer -
    multisetCharacteristicPolynomial consumer
  have mapped : difference.map (Polynomial.evalRingHom lambda)=0 := by
    dsimp only [difference]
    rw [Polynomial.map_sub,map_multisetCharacteristicPolynomial,
      map_multisetCharacteristicPolynomial,equal,sub_self]
  have coeffZero := congrArg (fun p : K[X] => p.coeff difference.natDegree) mapped
  simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coe_evalRingHom,
    lambdaError,Polynomial.leadingCoeff] using coeffZero

#print axioms natDegree_eq_zero_of_derivative_eq_zero_of_lt_char
#print axioms wronskian_ne_zero_of_distinct_monic_same_small_degree
#print axioms multisetCharacteristicPolynomial_injective
#print axioms eval_derivative_div_eval_multisetCharacteristicPolynomial
#print axioms multisetCharacteristicPolynomial_coeff_natDegree_le
#print axioms chiError_eval_zero
#print axioms chiError_nonzero
#print axioms chiError_degree
#print axioms chi_root_or_equal
#print axioms lambdaError_nonzero
#print axioms lambdaError_degree
#print axioms lambdaError_eval_zero
end
end AspisV8.SelectedCopyAliasCore
