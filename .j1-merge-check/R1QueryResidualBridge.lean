import R1MatchingSupport
import R1ResidualBatch
import R1NaturalEmbedding
import R1QueryAccumulator

/-! Deterministic connection from a 22-query residual check to the matching
support used by concrete two-fold binding. Queries may repeat in this file;
the probability law and distinct-query sampler are separate obligations. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryResidualBridge

open scoped BigOperators
open AspisCircleGroupOrder AspisV5FriDegreeThreeCorrelatedAgreement
open AspisR1.MatchingSupport

variable {K E : Type} [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]

def values (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1
    (AspisR1.parentIndex (q i))

def residuals (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => values d q i -
    AspisR1.ConcreteProjection.secondEncoder d.f (AspisR1.parentIndex (q i))

def rhoBad (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) : Finset K :=
  AspisR1.ResidualBatch.bad iota (residuals d q)

theorem rhoBad_card (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) :
    (rhoBad iota d q).card ≤ 21 :=
  AspisR1.ResidualBatch.bad_card_le_21 iota (residuals d q)

/-- Every queried position is in the complete two-equation matching support
when its first equation and the residual batch pass outside the counted set. -/
theorem queries_match (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val * residuals d q i = 0) :
    ∀ i, q i ∈ matchingSet d := by
  classical
  have hz := AspisR1.ResidualBatch.all_zero_of_eval_zero_outside_bad
    iota rho (residuals d q) hrho hbatch
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hfirst i, ?_⟩
  exact sub_eq_zero.mp (hz i)

/-- False deterministic claims force every successful query into the same
fixed support of size at most 9557, unless the rho residual exception occurs.
This is event containment, not a sampler or Fiat--Shamir probability bound. -/
theorem false_claims_query_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val * residuals d q i = 0) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d :=
  ⟨no_claims_card_le d hgood haccepted hnot,
    queries_match iota d q rho hrho hfirst hbatch⟩

variable [Algebra (ZMod P) K]

/-- The concrete log-16 natural basis, held in the challenge subfield. -/
def basis (q : Fin 22 → Fin 262144) : Fin 22 → Fin 64 → K :=
  fun i j => AspisCircleTensorBinding.naturalLineValue
    (algebraMap (ZMod P) K
      (AspisV5FriReleasedLineGeometry.storedLine16X
        (AspisR1.parentIndex (q i)))) j.val

theorem residuals_eq (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) :
    residuals d q = AspisR1.ResidualBatch.residual iota
      (values d q) d.f (basis (K := K) q) := by
  funext i
  unfold residuals AspisR1.ResidualBatch.residual
  rw [AspisR1.NaturalEmbedding.secondEncoder_query_eq_natural_sum iota d.f q i]
  rfl

/-- The final verifier equation in closed-sum form: 64 message coordinates
paired against K-valued accumulated basis columns equal the accumulated
second-fold values. This theorem derives the residual equation from it. -/
theorem accumulated_equation_implies_residual_batch (iota : K →+* E)
    (d : Data E) (q : Fin 22 → Fin 262144) (rho : K)
    (haccum : (∑ j : Fin 64, d.f j *
        iota (∑ i : Fin 22, rho ^ i.val * basis (K := K) q i j)) =
      ∑ i : Fin 22, (iota rho) ^ i.val * values d q i) :
    ∑ i : Fin 22, (iota rho) ^ i.val * residuals d q i = 0 := by
  rw [residuals_eq iota d q,
    AspisR1.ResidualBatch.weighted_residual_identity]
  exact sub_eq_zero.mpr haccum.symm

/-- Closed-sum verifier acceptance implies query containment outside the
21-element residual exception, with the same fixed matching support. -/
theorem accumulated_false_claims_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (haccum : (∑ j : Fin 64, d.f j *
        iota (∑ i : Fin 22, rho ^ i.val * basis (K := K) q i j)) =
      ∑ i : Fin 22, (iota rho) ^ i.val * values d q i) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d :=
  false_claims_query_containment iota d q rho hgood haccepted hnot hrho hfirst
    (accumulated_equation_implies_residual_batch iota d q rho haccum)

/-- Acceptance by the explicit 22-step arithmetic recurrence has the same
containment consequence. The recurrence uses canonical field elements; its
identification with Rust execution and checkpoint loading is still separate. -/
theorem recurrence_false_claims_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (haccum : (∑ j : Fin 64, d.f j * iota
        ((AspisR1.QueryAccumulator.run22 iota rho (values d q)
          (basis (K := K) q)).weights j)) =
      (AspisR1.QueryAccumulator.run22 iota rho (values d q)
        (basis (K := K) q)).rhs) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d := by
  simp_rw [AspisR1.QueryAccumulator.run22_weights,
    AspisR1.QueryAccumulator.run22_rhs] at haccum
  exact accumulated_false_claims_containment iota d q rho hgood haccepted hnot
    hrho hfirst haccum

#print axioms rhoBad_card
#print axioms queries_match
#print axioms false_claims_query_containment
#print axioms residuals_eq
#print axioms accumulated_equation_implies_residual_batch
#print axioms accumulated_false_claims_containment
#print axioms recurrence_false_claims_containment

end AspisR1.QueryResidualBridge
end
