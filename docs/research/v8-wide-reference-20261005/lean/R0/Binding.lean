import R0.BadSetBounds
import R0.OpeningAlgebra
import R0.FibreRestoration
import Wide.SubfieldDescent

/-! The opening-layer binding theorem over abstract committed words. No
Fiat--Shamir or semantic soundness statement is asserted. -/
set_option autoImplicit false
namespace AspisR0.Opening
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV6Width29CorrelatedAgreement AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriCoherentCandidateExtraction AspisV5ComponentCConcreteFoldLinearity
open AspisR0.RoundNormalization AspisR0.ChordImage AspisR0.Chord AspisR0.ChordGeometry
open AspisR0.ListsResponses AspisR0.Fold AspisR0.FibreRestoration
open AspisR0.PolynomialPair
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

attribute [local irreducible] Close Lambda LambdaR

theorem V1_iff_matching (D : Data K) (gamma alpha : K)
    (F : FinalMessage K) (S : Finset (Fin 262144)) :
    V1 D gamma alpha F S ↔ S ⊆ matchingFibres D gamma alpha F := by
  simp only [V1, matchingFibres, Finset.subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem foldWord_curve (R : InitialWord K) (alpha : K) (u : Fin 262144) :
    foldWord alpha R u = curveValue (channels R) alpha u := by
  simp only [foldWord, coefficientFoldValue, curveValue, AspisV5FunctionalBatching.batchedDiscrepancy]
  ring

theorem quotient_from_final (D : Data K) (gamma v kappa tau alpha : K)
    (P : K[X]) (F : FinalMessage K)
    (reconstruction : P.coeff 0+P.coeff 4 = quarter*claimPrime D gamma v kappa)
    (v2 : V2 D kappa tau alpha P F)
    (large : 9558 ≤ (matchingFibres D gamma alpha F).card)
    (h6 : alpha ∉ B6 (channels (batch D gamma))) (h7 : alpha ∉ B7 D gamma kappa tau P) :
    ∃ q ∈ Close (batch D gamma), dot (totalWeights D kappa tau) q = claimPrime D gamma v kappa := by
  let M := matchingFibres D gamma alpha F
  have hv : AlphaValid (channels (batch D gamma)) alpha (F,M) := by
    refine ⟨Nat.lt_of_lt_of_le (by decide : 9557 < 9558) large, ?_⟩
    intro u hu
    have he := (Finset.mem_filter.mp hu).2
    exact (foldWord_curve _ _ _).symm.trans he.symm
  obtain ⟨q,hq,hF⟩ := matched_close (batch D gamma) alpha F M large
    (alpha_match _ alpha h6 (F,M) hv)
  have he : P.eval alpha = (roundPolynomial q (totalWeights D kappa tau)).eval alpha := by
    rw [round_eval, ← hF]
    exact v2
  have same := B7_outside D gamma kappa tau alpha P h7 q hq he
  refine ⟨q,hq,?_⟩
  rw [dot_comm]
  exact AspisR0.Round.boundary_claim q (totalWeights D kappa tau) P _ same reconstruction

theorem recovered_encoder (D : Data K) (hne : D.z0 ≠ D.z1)
    (t : Fin 29 → InitialMessage K)
    (tails : ∀ i l, imageFunctional D i (t l) = 0) (l : Fin 29) :
    exactInitialEncoder (recovered D t l) = L D.z0 D.z1*exactInitialEncoder (t l)+
      exactInitialEncoder (interpolants D l) := by
  rw [recovered, exactInitialEncoder_add]
  rw [chordMessage_encoder _ _ _ (secant_nontrivial D.z0 D.z1 hne) (t l)
    (by simpa only [(image_functionals D (t l)).1] using tails 0 l)
    (by simpa only [(image_functionals D (t l)).2] using tails 1 l)]
  rfl

theorem recovered_joint (D : Data K) (hne : D.z0 ≠ D.z1)
    (h0 : ¬ BaseRational D.z0) (h1 : ¬ BaseRational D.z1)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ LambdaR (virtual D))
    (tails : ∀ i l, imageFunctional D i (t l) = 0) : recovered D t ∈ Lambda D.W := by
  rw [mem_Lambda]
  have bound : 38230 ≤ (width29JointAgreementSet exactInitialEncoder (virtual D) t).card :=
    (mem_Lambda _ _).mp (by simpa only [LambdaR] using ht)
  apply bound.trans (Finset.card_le_card ?_)
  intro i hi
  simp only [width29JointAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro l
  rw [recovered_encoder D hne t tails l]
  have hz := no_domain_zero D.z0 D.z1 hne h0 h1 i
  have hv := (div_eq_iff hz).mp (hi l)
  change D.W l i-exactInitialEncoder (interpolants D l) i = exactInitialEncoder (t l) i*L D.z0 D.z1 i at hv
  change D.W l i = L D.z0 D.z1 i*exactInitialEncoder (t l) i+exactInitialEncoder (interpolants D l) i
  linear_combination hv

theorem evalMessage_add (q r : InitialMessage K) (z : Point K) :
    evalMessage (q+r) z = evalMessage q z+evalMessage r z := by
  simp only [evalMessage, p0_add, p1_add, eval_add]
  ring

theorem recovered_values (D : Data K) (hne : D.z0 ≠ D.z1) (t : Fin 29 → InitialMessage K)
    (tails : ∀ i l, imageFunctional D i (t l) = 0) (l : Fin 29) :
    evalMessage (recovered D t l) D.z0 = D.y l 0 ∧
    evalMessage (recovered D t l) D.z1 = D.y l 1 := by
  have he1 : e1 (t l)=0 := (image_functionals D (t l)).1 ▸ tails 0 l
  have he2 : e2 (secantB D.z0 D.z1) (secantC D.z0 D.z1) (t l)=0 :=
    (image_functionals D (t l)).2 ▸ tails 1 l
  simp only [recovered, evalMessage_add, product_eval D.z0 D.z1 hne (t l) he1 he2,
    (secant_zeroes D.z0 D.z1).1, (secant_zeroes D.z0 D.z1).2, zero_mul, zero_add,
    interpolants, (interpolant_values D.z0 D.z1 hne (D.y l)).1,
    (interpolant_values D.z0 D.z1 hne (D.y l)).2, and_self]

theorem tuple_descent (D : Data K) (S : Fin 29 → Subfield K)
    (base : ∀ l i, D.W l i ∈ S l) (t : Fin 29 → InitialMessage K) (ht : t ∈ Lambda D.W) :
    ∀ l i, exactInitialEncoder (t l) i ∈ S l := by
  intro l
  have hb := (mem_Lambda D.W t).mp ht
  apply AspisWide.SubfieldDescent.initialCodeword_subfield_descent (S l) (D.W l) (t l)
    (width29JointAgreementSet exactInitialEncoder D.W t) (by omega)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact (h l).symm
  · exact base l

/-- §5: the coefficient comparison, image test, per-lane tests and field
of definition, for the exact encoders and every challenge/message variable. -/
theorem binding (D : Data K) (hne : D.z0 ≠ D.z1)
    (h0 : ¬ BaseRational D.z0) (h1 : ¬ BaseRational D.z1)
    (Sfield : Fin 29 → Subfield K) (base : ∀ l i, D.W l i ∈ Sfield l)
    (gamma v kappa tau alpha : K) (hnz : gamma ≠ 0)
    (P : K[X]) (F : FinalMessage K) (S : Finset (Fin 262144)) (semantic authentic : Prop)
    (accept : Accept D gamma v kappa tau alpha P F S semantic authentic)
    (h1bad : gamma ∉ B1 (virtual D)) (h2bad : gamma ∉ B2 D) (h3bad : gamma ∉ B3 D)
    (h4bad : kappa ∉ B4 D gamma v) (h5bad : tau ∉ B5 D gamma v kappa)
    (h6bad : alpha ∉ B6 (channels (batch D gamma))) (h7bad : alpha ∉ B7 D gamma kappa tau P)
    (large : 9558 ≤ (matchingFibres D gamma alpha F).card) :
    ∃ t ∈ Lambda D.W,
      (∀ l, evalMessage (t l) D.z0 = D.y l 0 ∧ evalMessage (t l) D.z1 = D.y l 1) ∧
      (∀ j l, D.pointClaims j l = dot (eqWeight (D.points j)) (t l)) ∧
      v = ∑ r ∈ D.inactive, exactInitialMessageCurve t gamma r ∧
      (∀ l i, exactInitialEncoder (t l) i ∈ Sfield l) := by
  obtain ⟨q,hq,hclaim⟩ := quotient_from_final D gamma v kappa tau alpha P F
    accept.2.2.2.1 accept.2.2.2.2.2 large h6bad h7bad
  have himage : (imagePolynomial D gamma v kappa q).eval tau = 0 := by
    rw [imagePolynomial_eval, hclaim, sub_self]
  obtain ⟨hpair,he0,he1⟩ := B5_outside D gamma v kappa tau h5bad q hq himage
  let A := agreementSet (batch D gamma) (exactInitialEncoder q)
  have hv : GammaValid (virtual D) gamma (q,A) := by
    refine ⟨?_,?_⟩
    · have hb : 38230 ≤ A.card := (mem_Close _ _).mp hq
      exact Nat.lt_of_lt_of_le (by decide : 38229 < 38230) hb
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  obtain ⟨t,ht,_,hqcurve⟩ := gamma_match (virtual D) gamma hnz h1bad (q,A) hv
  dsimp only at hqcurve
  have tails : ∀ i l, imageFunctional D i (t l) = 0 := by
    intro i l
    have hz : imageFunctional D i q = 0 := by
      fin_cases i
      · exact he0
      · exact he1
    rw [hqcurve, functional_curve] at hz
    exact congrFun (B2_outside D gamma hnz h2bad t ht i hz) l
  have hc := recovered_joint D hne h0 h1 t ht tails
  have batchedClaim : dot (weights D kappa) (exactInitialMessageCurve (recovered D t) gamma) = claim D gamma v kappa := by
    rw [recovered_curve, ← hqcurve, dot_add_right, quotient_pairing]
    change dot (qWeights D kappa) q+_ = _
    rw [hpair, claimPrime]
    ring
  have hpoly : (pointPolynomial D gamma v (recovered D t)).eval kappa = 0 := by
    rw [pointPolynomial_eval, batchedClaim, sub_self]
  have defects := B4_outside D gamma v kappa h4bad (recovered D t) hc hpoly
  have hI : inactiveDefect D gamma v (recovered D t) = 0 := by
    simpa only [pointPolynomial, eval_add, eval_C, eval_finsetSum, eval_monomial,
      congrFun defects, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hpoly
  refine ⟨recovered D t,hc,recovered_values D hne t tails,?_,?_,tuple_descent D Sfield base _ hc⟩
  · intro j l
    have hz := congrFun (B3_outside D gamma hnz h3bad _ hc j (congrFun defects j)) l
    exact sub_eq_zero.mp hz
  · have hi := sub_eq_zero.mp hI
    simpa only [inactiveDefect, indicator, dot, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter] using hi

theorem wideBinding : type_of% (@binding AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @binding AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms V1_iff_matching
#print axioms quotient_from_final
#print axioms recovered_joint
#print axioms recovered_values
#print axioms tuple_descent
#print axioms binding
#print axioms wideBinding
end
end AspisR0.Opening
