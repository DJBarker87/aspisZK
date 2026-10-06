import R0.Fold

/-! Historical counterexamples below refute only the unscaled form, corrected
by owner decision in cd5eb4226. The quarter-scaled identities are current F5.

The V8 module cannot be imported alongside Wide: its NaturalBasisCore
redeclares constants from the pinned V7 CircleNaturalBasis. RoundCore and
KernelCorrespondence now provide a shared formula bridge. -/
set_option autoImplicit false
namespace AspisR0.RoundNormalization
open Polynomial
open AspisR0.Fold
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5ComponentCConcreteFoldLinearity
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def quarter : K := (4 : K)⁻¹

/-- The dual fold in the cited R370 theorem, without an added factor. -/
def citedDualFold (alpha : K) (w : InitialMessage K) (d : Fin 256) : K :=
  ∑ t : Fin 4, w (childIndex d t) * alpha ^ ((4 - t.val) % 4)

def dot {n : Nat} (q w : Fin n → K) : K := ∑ i, q i * w i

/-- The polynomial with the source-kernel coefficients of R370/R653. -/
def roundPolynomial (q w : InitialMessage K) : K[X] :=
  ∑ d : Fin 256, ∑ s : Fin 4, ∑ t : Fin 4,
    monomial (s.val + (4 - t.val) % 4)
      (quarter * q (childIndex d s) * w (childIndex d t))

theorem foldMessage_eq_sum (alpha : K) (q : InitialMessage K) (d : Fin 256) :
    foldMessage alpha q d = ∑ s : Fin 4, q (childIndex d s) * alpha ^ s.val := by
  simp only [foldMessage, coefficientFoldLayer_apply, coefficientFoldValue,
    Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl,
    pow_zero, pow_one, mul_one]
  ring

theorem round_degree (q w : InitialMessage K) : (roundPolynomial q w).natDegree ≤ 6 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  apply (Polynomial.natDegree_monomial_le _).trans
  have hs := s.isLt
  have ht := Nat.mod_lt (4 - t.val) (by decide : 0 < 4)
  omega

theorem round_eval (alpha : K) (q w : InitialMessage K) :
    (roundPolynomial q w).eval alpha =
      quarter * dot (foldMessage alpha q) (citedDualFold alpha w) := by
  simp only [roundPolynomial, eval_finsetSum, eval_monomial, dot,
    foldMessage_eq_sum, citedDualFold, Finset.mul_sum, Finset.sum_mul, pow_add]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem round_boundary (q w : InitialMessage K) :
    (roundPolynomial q w).coeff 0 + (roundPolynomial q w).coeff 4 =
      quarter * dot q w := by
  have reindex : dot q w =
      ∑ d : Fin 256, ∑ s : Fin 4, q (childIndex d s) * w (childIndex d s) := by
    rw [dot, ← (fibreIndexEquiv 256).sum_comp, Fintype.sum_prod_type]
    rfl
  rw [reindex, roundPolynomial]
  simp only [finsetSum_coeff, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp [Fin.sum_univ_four, coeff_monomial]
  ring

/-- Both identities actually supplied by the cited source-kernel convention. -/
theorem cited_round_identities (q w : InitialMessage K) :
    (roundPolynomial q w).natDegree ≤ 6 ∧
    (∀ alpha, (roundPolynomial q w).eval alpha =
      quarter * dot (foldMessage alpha q) (citedDualFold alpha w)) ∧
    (roundPolynomial q w).coeff 0 + (roundPolynomial q w).coeff 4 =
      quarter * dot q w :=
  ⟨round_degree q w, fun alpha => round_eval alpha q w, round_boundary q w⟩

def unitMessage : InitialMessage K := fun i => if i = 0 then 1 else 0

theorem childIndex_eq_zero_iff (d : Fin 256) (s : Fin 4) :
    childIndex d s = (0 : Fin 1024) ↔ d = 0 ∧ s = 0 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [childIndex_val, Fin.val_zero] at hv
    constructor <;> apply Fin.ext <;> simp only [Fin.val_zero] <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem unit_folds (alpha : K) :
    foldMessage alpha (unitMessage (K := K)) = (fun d => if d = 0 then 1 else 0) ∧
    citedDualFold alpha (unitMessage (K := K)) = (fun d => if d = 0 then 1 else 0) := by
  constructor
  · funext d
    rw [foldMessage_eq_sum]
    simp only [unitMessage]
    by_cases hd : d = 0 <;> simp [childIndex, hd]
  · funext d
    simp only [citedDualFold, unitMessage]
    by_cases hd : d = 0 <;> simp [childIndex, hd]

theorem quarter_ne_one : quarter (K := K) ≠ 1 := by
  have threeNonzero : (3 : K) ≠ 0 := by
    intro h
    have hb : (3 : ZMod AspisCircleGroupOrder.P) = 0 := by
      apply FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
      simpa only [map_ofNat, map_zero] using h
    have bad := (CharP.cast_eq_zero_iff (ZMod AspisCircleGroupOrder.P)
      AspisCircleGroupOrder.P 3).mp hb
    have small : 3 < AspisCircleGroupOrder.P := by norm_num [AspisCircleGroupOrder.P]
    exact (Nat.not_dvd_of_pos_of_lt (by omega) small) bad
  intro h
  have fourOne : (4 : K) = 1 := inv_eq_one.mp h
  apply threeNonzero
  linear_combination fourOne

/-- Historical counterexample to the former unscaled equality, corrected in
cd5eb4226; q=w is the first coordinate vector. -/
theorem unscaled_F5_counterexample (alpha : K) :
    (roundPolynomial (unitMessage (K := K)) unitMessage).eval alpha = quarter ∧
    dot (foldMessage alpha (unitMessage (K := K)))
      (citedDualFold alpha unitMessage) = 1 ∧
    (roundPolynomial (unitMessage (K := K)) unitMessage).eval alpha ≠
      dot (foldMessage alpha unitMessage) (citedDualFold alpha unitMessage) := by
  have pair : dot (foldMessage alpha (unitMessage (K := K)))
      (citedDualFold alpha unitMessage) = 1 := by
    rw [(unit_folds alpha).1, (unit_folds alpha).2]
    simp [dot]
  have value : (roundPolynomial (unitMessage (K := K)) unitMessage).eval alpha = quarter := by
    rw [round_eval, pair, mul_one]
  exact ⟨value, pair, by rw [value, pair]; exact quarter_ne_one⟩

/-- The formerly blocked inference in §5 (resolved in cd5eb4226): the unscaled (V2) and the prescribed
coefficient reconstruction can both hold, while the evaluation equality
needed to invoke exclusion from B7 fails. This is a local counterexample to
that inference, not an assertion that a complete R0 transcript exists. -/
theorem comparison_step_counterexample :
    ∃ claimed : K[X], claimed.natDegree ≤ 6 ∧
      claimed.coeff 0 + claimed.coeff 4 = quarter * (4 : K) ∧
      ∀ alpha : K,
        claimed.eval alpha = dot (foldMessage alpha unitMessage)
          (citedDualFold alpha unitMessage) ∧
        claimed.eval alpha ≠ (roundPolynomial unitMessage unitMessage).eval alpha := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have h := mul_ne_zero (AspisWide.InitialEncoder.two_ne_zero (K := K))
      (AspisWide.InitialEncoder.two_ne_zero (K := K))
    norm_num at h ⊢
    exact h
  refine ⟨1, by simp, ?_, ?_⟩
  · norm_num [quarter, Polynomial.coeff_one, inv_mul_cancel₀ fourNonzero]
  · intro alpha
    obtain ⟨value, pair, _⟩ := unscaled_F5_counterexample (K := K) alpha
    constructor
    · simpa only [Polynomial.eval_one] using pair.symm
    · simpa only [Polynomial.eval_one, value] using (quarter_ne_one (K := K)).symm

theorem wide_cited_round_identities :
    type_of% (@cited_round_identities AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @cited_round_identities AspisWideTower.WideExact _ _ (Classical.decEq _) _

theorem wide_unscaled_F5_counterexample :
    type_of% (@unscaled_F5_counterexample AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @unscaled_F5_counterexample AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms cited_round_identities
#print axioms unscaled_F5_counterexample
#print axioms comparison_step_counterexample
#print axioms wide_cited_round_identities
#print axioms wide_unscaled_F5_counterexample
end
end AspisR0.RoundNormalization
