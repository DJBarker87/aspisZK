import R1QueryResidualBridge
import AspisFinalSumcheckModel

/-! The Aspis one-transaction verifier: the residual pair under the batching
challenge, stated over R1's matching-support data.

Kind of result: MATHEMATICAL MODEL THEOREMS over R1's `MatchingSupport.Data`
(the literal committed words `W` (C1 and C2 lanes) and `V` (folded tree), the
final message `f` and the challenges) and an ordered query vector. No
probability, Fiat--Shamir, binding or source statement is made here. Binding
(why the data are the committed words for every accepting run) is in
`AspisPairResidualObservation` and `AspisPairResidualMerkle`; the row-32
sampler density is in `AspisPairResidualDensity`.

What it establishes.
* `firstResiduals d q`: the first-fold residuals `F_i - b_i`, with
  `F_i = foldWord alpha0 (batchedWord W gamma) (q i)` and `b_i = V (q i)`.
  `firstResiduals d q i = 0` is exactly R1's `match0 d (q i)`.
* `pairBad iota d q := StageD.bad2 iota (firstResiduals d q) (residuals d q)`,
  at most 21 elements (`pairBad_card`).
* Outside `pairBad`, the two batched equalities give R1's per-query
  first-fold equality at every query AND R1's residual-batch equation, hence
  R1's `queries_match` and `false_claims_query_containment` conclusions
  (`pair_queries_match`, `pair_false_claims_query_containment`).
* R1 recovered: when every first-fold residual is zero (R1 checks them one by
  one), `pairBad = rhoBad` (`pairBad_eq_rhoBad_of_match0`), and R1's own
  `queries_match` is re-derived from the pair theorem
  (`queries_match_from_pair`). -/

set_option autoImplicit false
noncomputable section
namespace AspisPairResidual

open scoped BigOperators
open AspisCircleGroupOrder
open AspisR1.MatchingSupport

variable {K E : Type} [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]

/-- First-fold residual of query `i`: the first fold of the gamma-batched
initial word at the queried position minus the folded word's value there. -/
def firstResiduals (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => AspisR1.FirstFold.foldWord d.alpha0
      (AspisR1.TwoFoldExtraction.batchedWord d.W d.gamma) (q i) - d.V (q i)

/-- The batching-challenge bad set for the residual pair. -/
def pairBad (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) : Finset K :=
  AspisFuture.StageD.bad2 iota (firstResiduals d q)
    (AspisR1.QueryResidualBridge.residuals d q)

theorem pairBad_card (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) :
    (pairBad iota d q).card ≤ 21 :=
  AspisFuture.StageD.bad2_card_le_21 iota _ _

theorem firstResidual_eq_zero_iff (d : Data E) (q : Fin 22 → Fin 262144) (i : Fin 22) :
    firstResiduals d q i = 0 ↔ match0 d (q i) := by
  unfold firstResiduals match0
  exact sub_eq_zero

/-- The verifier's batched first-fold equality `sum rho^i F_i = sum rho^i b_i`
is the vanishing of the batched first-fold residual. -/
theorem batched_first_iff (iota : K →+* E) (rho : K) (d : Data E)
    (q : Fin 22 → Fin 262144) :
    (∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0) ↔
      (∑ i : Fin 22, (iota rho) ^ i.val * AspisR1.FirstFold.foldWord d.alpha0
          (AspisR1.TwoFoldExtraction.batchedWord d.W d.gamma) (q i)) =
        ∑ i : Fin 22, (iota rho) ^ i.val * d.V (q i) := by
  unfold firstResiduals
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero

theorem residualPolynomial_same (r : Fin 22 → E) :
    AspisFuture.StageD.residualPolynomial r = AspisR1.ResidualBatch.residualPolynomial r := rfl

/-- R1 is the case of zero first-fold residuals: the pair set is R1's set. -/
theorem pairBad_eq_rhoBad_of_match0 (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (hfirst : ∀ i, match0 d (q i)) :
    pairBad iota d q = AspisR1.QueryResidualBridge.rhoBad iota d q := by
  classical
  have hz : ∀ i, firstResiduals d q i = 0 := fun i =>
    (firstResidual_eq_zero_iff d q i).mpr (hfirst i)
  have h0 : AspisFuture.StageD.residualPolynomial (firstResiduals d q) = 0 :=
    (AspisFuture.StageD.residualPolynomial_eq_zero_iff _).mpr hz
  unfold pairBad AspisFuture.StageD.bad2 AspisR1.QueryResidualBridge.rhoBad
    AspisR1.ResidualBatch.bad
  rw [if_neg (not_not.mpr h0)]
  by_cases h1 : AspisR1.ResidualBatch.residualPolynomial
      (AspisR1.QueryResidualBridge.residuals d q) = 0
  · have h1' : AspisFuture.StageD.residualPolynomial
        (AspisR1.QueryResidualBridge.residuals d q) = 0 := h1
    rw [if_neg (not_not.mpr h1'), if_pos h1]
  · have h1' : AspisFuture.StageD.residualPolynomial
        (AspisR1.QueryResidualBridge.residuals d q) ≠ 0 := h1
    rw [if_pos h1', if_neg h1]
    ext x
    unfold AspisFuture.StageD.rootsIn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

/-- Both batched equalities outside the pair set give all 44 per-query
equalities: R1's first-fold equality at every query and every second-fold
residual zero. -/
theorem pair_all_zero (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144)
    (rho : K) (hrho : rho ∉ pairBad iota d q)
    (h0 : ∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0)
    (h1 : ∑ i : Fin 22, (iota rho) ^ i.val *
      AspisR1.QueryResidualBridge.residuals d q i = 0) :
    (∀ i, match0 d (q i)) ∧ (∀ i, AspisR1.QueryResidualBridge.residuals d q i = 0) := by
  have hz := AspisFuture.StageD.all_zero_of_both_evals_zero_outside_bad2 iota rho
    (firstResiduals d q) (AspisR1.QueryResidualBridge.residuals d q) hrho h0 h1
  exact ⟨fun i => (firstResidual_eq_zero_iff d q i).mp (hz.1 i), hz.2⟩

/-- Aspis form of R1's `queries_match`: the per-query first-fold premise
`hfirst` is replaced by the batched first-fold equality, and `rhoBad` by
`pairBad`. The proof goes through R1's own theorem. -/
theorem pair_queries_match (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hrho : rho ∉ pairBad iota d q)
    (h0 : ∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0)
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val *
      AspisR1.QueryResidualBridge.residuals d q i = 0) :
    ∀ i, q i ∈ matchingSet d := by
  have hfirst := (pair_all_zero iota d q rho hrho h0 hbatch).1
  have hrho' : rho ∉ AspisR1.QueryResidualBridge.rhoBad iota d q := by
    rw [← pairBad_eq_rhoBad_of_match0 iota d q hfirst]
    exact hrho
  exact AspisR1.QueryResidualBridge.queries_match iota d q rho hrho' hfirst hbatch

/-- Aspis form of R1's `false_claims_query_containment`. -/
theorem pair_false_claims_query_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ pairBad iota d q)
    (h0 : ∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0)
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val *
      AspisR1.QueryResidualBridge.residuals d q i = 0) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d :=
  ⟨no_claims_card_le d hgood haccepted hnot,
    pair_queries_match iota d q rho hrho h0 hbatch⟩

/-- Check against R1: R1's `queries_match` follows from the pair theorem
(its per-query premise makes the batched first-fold residual vanish and the
pair set equal to R1's set). -/
theorem queries_match_from_pair (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hrho : rho ∉ AspisR1.QueryResidualBridge.rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val *
      AspisR1.QueryResidualBridge.residuals d q i = 0) :
    ∀ i, q i ∈ matchingSet d := by
  have h0 : ∑ i : Fin 22, (iota rho) ^ i.val * firstResiduals d q i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [(firstResidual_eq_zero_iff d q i).mpr (hfirst i), mul_zero]
  have hrho' : rho ∉ pairBad iota d q := by
    rw [pairBad_eq_rhoBad_of_match0 iota d q hfirst]
    exact hrho
  exact pair_queries_match iota d q rho hrho' h0 hbatch

variable [Algebra (ZMod P) K]

/-- The verifier's two batched checks in the closed-sum form the code
computes (`lhs1 = rhs1`; R1's accumulated final equation for `rhs2`). -/
theorem pair_accumulated_false_claims_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ pairBad iota d q)
    (hfirstBatch : (∑ i : Fin 22, (iota rho) ^ i.val * AspisR1.FirstFold.foldWord d.alpha0
          (AspisR1.TwoFoldExtraction.batchedWord d.W d.gamma) (q i)) =
        ∑ i : Fin 22, (iota rho) ^ i.val * d.V (q i))
    (haccum : (∑ j : Fin 64, d.f j *
        iota (∑ i : Fin 22, rho ^ i.val *
          AspisR1.QueryResidualBridge.basis (K := K) q i j)) =
      ∑ i : Fin 22, (iota rho) ^ i.val * AspisR1.QueryResidualBridge.values d q i) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d :=
  pair_false_claims_query_containment iota d q rho hgood haccepted hnot hrho
    ((batched_first_iff iota rho d q).mpr hfirstBatch)
    (AspisR1.QueryResidualBridge.accumulated_equation_implies_residual_batch
      iota d q rho haccum)

#print axioms pairBad_card
#print axioms firstResidual_eq_zero_iff
#print axioms batched_first_iff
#print axioms residualPolynomial_same
#print axioms pairBad_eq_rhoBad_of_match0
#print axioms pair_all_zero
#print axioms pair_queries_match
#print axioms pair_false_claims_query_containment
#print axioms queries_match_from_pair
#print axioms pair_accumulated_false_claims_containment

end AspisPairResidual
end
