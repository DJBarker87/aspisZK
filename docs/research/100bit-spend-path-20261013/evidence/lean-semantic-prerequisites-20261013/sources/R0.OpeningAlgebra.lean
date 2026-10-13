import R0.OpeningDefinitions

set_option autoImplicit false
namespace AspisR0.Opening
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisV6Width29CorrelatedAgreement
open AspisR0.RoundNormalization AspisR0.ChordImage AspisR0.Chord AspisR0.ChordGeometry
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem dot_comm {n : Nat} (w q : Fin n → K) : dot w q = dot q w := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _
theorem dot_add_left {n : Nat} (a b q : Fin n → K) : dot (a+b) q = dot a q+dot b q := add_dotProduct _ _ _
theorem dot_add_right {n : Nat} (w a b : Fin n → K) : dot w (a+b) = dot w a+dot w b := dotProduct_add _ _ _
theorem dot_smul_left {n : Nat} (k : K) (w q : Fin n → K) : dot (k • w) q = k*dot w q := smul_dotProduct _ _ _
theorem dot_smul_right {n : Nat} (k : K) (w q : Fin n → K) : dot w (k • q) = k*dot w q := dotProduct_smul _ _ _

theorem dot_sum_left {ι : Type*} (s : Finset ι) (w : ι → InitialMessage K)
    (m : InitialMessage K) : dot (∑ i ∈ s, w i) m = ∑ i ∈ s, dot (w i) m :=
  sum_dotProduct _ _ _

theorem dot_curve (w : InitialMessage K) (t : Fin 29 → InitialMessage K) (gamma : K) :
    dot w (exactInitialMessageCurve t gamma) = width29Batch (fun l => dot w (t l)) gamma := by
  unfold exactInitialMessageCurve
  rw [show dot w (∑ l, gamma^l.val • t l) = ∑ l, dot w (gamma^l.val • t l) from dotProduct_sum _ _ _]
  simp only [dot_smul_right, width29Batch]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem functional_curve (e : InitialMessage K →ₗ[K] K) (t : Fin 29 → InitialMessage K) (gamma : K) :
    e (exactInitialMessageCurve t gamma) = width29Batch (fun l => e (t l)) gamma := by
  simp only [exactInitialMessageCurve, map_sum, map_smul, smul_eq_mul, width29Batch]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pointDefect_eq (D : Data K) (gamma : K) (t : Fin 29 → InitialMessage K) (j : Fin 3) :
    pointDefect D gamma t j = width29Batch (D.pointClaims j) gamma-
      dot (coeffWeight D.transport (eqWeight (D.points j))) (exactInitialMessageCurve t gamma) := by
  rw [dot_curve]
  simp only [pointDefect, width29Batch, discrepancy, sub_mul, Finset.sum_sub_distrib]

theorem extraDefect_eq (D : Data K) (gamma : K) (t : Fin 29 → InitialMessage K) :
    extraDefect D gamma t = width29Batch D.extraClaims gamma-
      dot D.extraWeight (exactInitialMessageCurve t gamma) := by
  rw [dot_curve]
  simp only [extraDefect, width29Batch, extraDiscrepancy, sub_mul, Finset.sum_sub_distrib]

theorem pointPolynomial_eval (D : Data K) (gamma v kappa : K) (t : Fin 29 → InitialMessage K) :
    (pointPolynomial D gamma v t).eval kappa =
      claim D gamma v kappa-dot (weights D kappa) (exactInitialMessageCurve t gamma) := by
  simp only [pointPolynomial, eval_add, eval_C, eval_finsetSum, eval_monomial,
    pointDefect_eq, extraDefect_eq, claim, weights, coeffWeight_add, coeffWeight_sum,
    coeffWeight_smul, dot_add_left, dot_sum_left, dot_smul_left, inactiveDefect,
    mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp_rw [mul_comm (width29Batch _ gamma), mul_comm (dot _ _)]
  ring

theorem total_pairing (D : Data K) (kappa tau : K) (q : InitialMessage K) :
    dot (totalWeights D kappa tau) q = dot (qWeights D kappa) q+
      tau*imageFunctional D 0 q+tau^2*imageFunctional D 1 q := by
  have row (e : InitialMessage K →ₗ[K] K) : dot (FunctionalWeights.row e) q = e q :=
    FunctionalWeights.row_pairing e q
  simp only [totalWeights, dot_add_left, dot_smul_left, row]

theorem imagePolynomial_eval (D : Data K) (gamma v kappa tau : K) (q : InitialMessage K) :
    (imagePolynomial D gamma v kappa q).eval tau =
      dot (totalWeights D kappa tau) q-claimPrime D gamma v kappa := by
  simp only [imagePolynomial, eval_add, eval_C, eval_monomial, pow_one, total_pairing]
  ring

theorem image_functionals (D : Data K) (q : InitialMessage K) :
    imageFunctional D 0 q = e1 q ∧
    imageFunctional D 1 q = e2 (secantB D.z0 D.z1) (secantC D.z0 D.z1) q := by
  simp [imageFunctional]

def recovered (D : Data K) (t : Fin 29 → InitialMessage K) : Fin 29 → InitialMessage K :=
  fun l => chordMessage (secantA D.z0 D.z1) (secantB D.z0 D.z1) (secantC D.z0 D.z1) (t l)+interpolants D l

theorem recovered_curve (D : Data K) (t : Fin 29 → InitialMessage K) (gamma : K) :
    exactInitialMessageCurve (recovered D t) gamma =
      chordMessage (secantA D.z0 D.z1) (secantB D.z0 D.z1) (secantC D.z0 D.z1)
        (exactInitialMessageCurve t gamma)+exactInitialMessageCurve (interpolants D) gamma := by
  have h := map_sum (chordLinear (secantA D.z0 D.z1) (secantB D.z0 D.z1) (secantC D.z0 D.z1))
    (fun l : Fin 29 => gamma^l.val • t l) Finset.univ
  simp only [map_smul, RingHom.id_apply] at h
  change chordMessage _ _ _ (exactInitialMessageCurve t gamma) =
    ∑ l, gamma^l.val • chordMessage _ _ _ (t l) at h
  rw [h]
  simp only [exactInitialMessageCurve, recovered, smul_add, Finset.sum_add_distrib]

#print axioms pointPolynomial_eval
#print axioms imagePolynomial_eval
#print axioms recovered_curve
end
end AspisR0.Opening
