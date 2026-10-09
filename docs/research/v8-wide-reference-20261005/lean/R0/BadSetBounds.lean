import R0.OpeningDefinitions

set_option autoImplicit false
namespace AspisR0.Opening
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV6Width29CorrelatedAgreement
open AspisR0.ListsResponses AspisR0.RoundNormalization AspisR0.RootCounts
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

attribute [local irreducible] Close Lambda LambdaR

theorem batch_union_bound {ι J : Type*} [DecidableEq ι] [Fintype J]
    (s : Finset ι) (values : ι → J → Fin 29 → K) :
    (s.biUnion fun t => Finset.univ.biUnion fun j =>
      if values t j = 0 then ∅ else width29NonzeroCollisionSet (values t j)).card ≤
      s.card * Fintype.card J * 28 := by
  classical
  calc
    _ ≤ ∑ t ∈ s, (Finset.univ.biUnion fun j =>
      if values t j = 0 then ∅ else width29NonzeroCollisionSet (values t j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ s, Fintype.card J * 28 := by
      apply Finset.sum_le_sum
      intro t _
      calc
        _ ≤ ∑ j : J, (if values t j = 0 then ∅ else width29NonzeroCollisionSet (values t j)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _j : J, 28 := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs with h
          · simp
          · exact width29_nonzero_collision_card_le _ h
        _ = _ := by simp
    _ = _ := by simp [Nat.mul_assoc]

theorem B2_card (D : Data K) : (B2 D).card ≤ 5600 := by
  have h := batch_union_bound (LambdaR (virtual D)) (fun t i l => imageFunctional D i (t l))
  have hc := LambdaR_card (virtual D)
  change (B2 D).card ≤ _ at h
  simp only [Fintype.card_fin] at h
  omega

theorem B3_card (D : Data K) : (B3 D).card ≤ 11200 := by
  classical
  have points (t : Fin 29 → InitialMessage K) :
      (Finset.univ.biUnion fun j : Fin 3 =>
        if discrepancy D t j = 0 then ∅ else width29NonzeroCollisionSet (discrepancy D t j)).card ≤ 84 := by
    simpa using batch_union_bound {t} (discrepancy D)
  have extra (t : Fin 29 → InitialMessage K) :
      (if extraDiscrepancy D t = 0 then ∅ else
        width29NonzeroCollisionSet (extraDiscrepancy D t)).card ≤ 28 := by
    split_ifs with h
    · simp
    · exact width29_nonzero_collision_card_le _ h
  calc
    (B3 D).card ≤ ∑ t ∈ Lambda D.W,
        ((Finset.univ.biUnion fun j : Fin 3 =>
          if discrepancy D t j = 0 then ∅ else width29NonzeroCollisionSet (discrepancy D t j)) ∪
          (if extraDiscrepancy D t = 0 then ∅ else
            width29NonzeroCollisionSet (extraDiscrepancy D t))).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Lambda D.W, 112 := by
      apply Finset.sum_le_sum
      intro t _
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add (points t) (extra t))
    _ ≤ 11200 := by
      have hc := Lambda_card D.W
      simp only [Finset.sum_const, smul_eq_mul]
      omega

theorem B2_outside (D : Data K) (gamma : K) (hnz : gamma ≠ 0) (hg : gamma ∉ B2 D)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ LambdaR (virtual D)) (i : Fin 2)
    (zero : width29Batch (fun l => imageFunctional D i (t l)) gamma = 0) :
    (fun l => imageFunctional D i (t l)) = 0 := by
  classical
  by_contra h
  apply hg
  simp only [B2, Finset.mem_biUnion]
  refine ⟨t, ht, i, Finset.mem_univ i, ?_⟩
  rw [if_neg h]
  simp [width29NonzeroCollisionSet, hnz, zero]

theorem B3_outside (D : Data K) (gamma : K) (hnz : gamma ≠ 0) (hg : gamma ∉ B3 D)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ Lambda D.W) (j : Fin 3)
    (zero : pointDefect D gamma t j = 0) : discrepancy D t j = 0 := by
  classical
  by_contra h
  apply hg
  simp only [B3, Finset.mem_biUnion]
  refine ⟨t, ht, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩)⟩
  rw [if_neg h]
  simpa [width29NonzeroCollisionSet, hnz, pointDefect] using zero

theorem B3_extra_outside (D : Data K) (gamma : K) (hnz : gamma ≠ 0) (hg : gamma ∉ B3 D)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ Lambda D.W)
    (zero : extraDefect D gamma t = 0) : extraDiscrepancy D t = 0 := by
  classical
  by_contra h
  apply hg
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ht, Finset.mem_union_right _ ?_⟩
  rw [if_neg h]
  simpa [width29NonzeroCollisionSet, hnz, extraDefect] using zero

theorem pointPolynomial_degree (D : Data K) (gamma v : K) (t : Fin 29 → InitialMessage K) :
    (pointPolynomial D gamma v t).natDegree ≤ 4 := by
  simp only [pointPolynomial, Fin.sum_univ_succ]
  compute_degree

theorem pointPolynomial_coeff (D : Data K) (gamma v : K) (t : Fin 29 → InitialMessage K) (j : Fin 3) :
    (pointPolynomial D gamma v t).coeff (j.val+1) = pointDefect D gamma t j := by
  fin_cases j <;> simp [pointPolynomial, Fin.sum_univ_succ, coeff_monomial]

theorem pointPolynomial_extra_coeff (D : Data K) (gamma v : K) (t : Fin 29 → InitialMessage K) :
    (pointPolynomial D gamma v t).coeff 4 = extraDefect D gamma t := by
  simp [pointPolynomial, Fin.sum_univ_succ, coeff_monomial]

theorem B4_card (D : Data K) (gamma v : K) : (B4 D gamma v).card ≤ 400 := by
  classical
  have subset : B4 D gamma v ⊆ (Lambda D.W).biUnion (fun t => badRoots (pointPolynomial D gamma v t)) := by
    intro k hk
    obtain ⟨t,ht,hd,he⟩ := (Finset.mem_filter.mp hk).2
    apply Finset.mem_biUnion.mpr
    refine ⟨t,ht,(mem_badRoots _ _).mpr ⟨?_,he⟩⟩
    intro hz
    rcases hd with hd | hd
    · apply hd
      funext j
      have hc := congrArg (fun p : K[X] => p.coeff (j.val+1)) hz
      simpa only [pointPolynomial_coeff, coeff_zero, Pi.zero_apply] using hc
    · apply hd
      have hc := congrArg (fun p : K[X] => p.coeff 4) hz
      simpa only [pointPolynomial_extra_coeff, coeff_zero] using hc
  have bound := union_bound (Lambda D.W) (pointPolynomial D gamma v) 4
    (fun t _ => pointPolynomial_degree D gamma v t)
  have hc := Lambda_card D.W
  exact (Finset.card_le_card subset).trans (bound.trans (by omega))

theorem B4_outside (D : Data K) (gamma v kappa : K) (hg : kappa ∉ B4 D gamma v)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ Lambda D.W)
    (he : (pointPolynomial D gamma v t).eval kappa = 0) :
    pointDefect D gamma t = 0 ∧ extraDefect D gamma t = 0 := by
  classical
  constructor
  · by_contra hd
    exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,ht,Or.inl hd,he⟩)
  · by_contra hd
    exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,ht,Or.inr hd,he⟩)

theorem imagePolynomial_degree (D : Data K) (gamma v kappa : K) (q : InitialMessage K) :
    (imagePolynomial D gamma v kappa q).natDegree ≤ 2 := by
  unfold imagePolynomial
  compute_degree

theorem imagePolynomial_zero_iff (D : Data K) (gamma v kappa : K) (q : InitialMessage K) :
    imagePolynomial D gamma v kappa q = 0 ↔
      dot (qWeights D kappa) q = claimPrime D gamma v kappa ∧
      imageFunctional D 0 q = 0 ∧ imageFunctional D 1 q = 0 := by
  constructor
  · intro h
    have c0 := congrArg (fun p : K[X] => p.coeff 0) h
    have c1 := congrArg (fun p : K[X] => p.coeff 1) h
    have c2 := congrArg (fun p : K[X] => p.coeff 2) h
    simp [imagePolynomial, coeff_monomial] at c0 c1 c2
    exact ⟨sub_eq_zero.mp c0,c1,c2⟩
  · rintro ⟨h0,h1,h2⟩
    simp [imagePolynomial,h0,h1,h2]

theorem B5_card (D : Data K) (gamma v kappa : K) : (B5 D gamma v kappa).card ≤ 200 := by
  have h := union_bound (Close (batch D gamma)) (imagePolynomial D gamma v kappa) 2
    (fun q _ => imagePolynomial_degree D gamma v kappa q)
  have hc := Close_card (batch D gamma)
  exact h.trans (by omega)

theorem B5_outside (D : Data K) (gamma v kappa tau : K) (hg : tau ∉ B5 D gamma v kappa)
    (q : InitialMessage K) (hq : q ∈ Close (batch D gamma))
    (he : (imagePolynomial D gamma v kappa q).eval tau = 0) :
      dot (qWeights D kappa) q = claimPrime D gamma v kappa ∧
      imageFunctional D 0 q = 0 ∧ imageFunctional D 1 q = 0 := by
  apply (imagePolynomial_zero_iff D gamma v kappa q).mp
  by_contra hz
  exact hg (Finset.mem_biUnion.mpr ⟨q,hq,(mem_badRoots _ _).mpr ⟨hz,he⟩⟩)

theorem B7_card (D : Data K) (gamma kappa tau : K) (P : K[X]) (hp : P.natDegree ≤ 6) :
    (B7 D gamma kappa tau P).card ≤ 600 := by
  have h := union_bound (Close (batch D gamma))
    (fun q => P-roundPolynomial q (totalWeights D kappa tau)) 6 (fun q _ =>
      (natDegree_sub_le _ _).trans (max_le hp (round_degree _ _)))
  have hc := Close_card (batch D gamma)
  exact h.trans (by omega)

theorem B7_outside (D : Data K) (gamma kappa tau alpha : K) (P : K[X])
    (hg : alpha ∉ B7 D gamma kappa tau P) (q : InitialMessage K) (hq : q ∈ Close (batch D gamma))
    (he : P.eval alpha = (roundPolynomial q (totalWeights D kappa tau)).eval alpha) :
    P = roundPolynomial q (totalWeights D kappa tau) := by
  by_contra hn
  apply hg
  apply Finset.mem_biUnion.mpr
  exact ⟨q,hq,(mem_badRoots _ _).mpr ⟨sub_ne_zero.mpr hn, by simp [eval_sub,he]⟩⟩

theorem mem_B5_iff (D : Data K) (gamma v kappa tau : K) :
    tau ∈ B5 D gamma v kappa ↔ ∃ q ∈ Close (batch D gamma),
      ¬ (dot (qWeights D kappa) q = claimPrime D gamma v kappa ∧
        imageFunctional D 0 q = 0 ∧ imageFunctional D 1 q = 0) ∧
      (imagePolynomial D gamma v kappa q).eval tau = 0 := by
  classical
  simp only [B5, Finset.mem_biUnion, mem_badRoots, ne_eq, imagePolynomial_zero_iff]

theorem mem_B7_iff (D : Data K) (gamma kappa tau alpha : K) (P : K[X]) :
    alpha ∈ B7 D gamma kappa tau P ↔ ∃ q ∈ Close (batch D gamma),
      P ≠ roundPolynomial q (totalWeights D kappa tau) ∧
      P.eval alpha = (roundPolynomial q (totalWeights D kappa tau)).eval alpha := by
  classical
  simp only [B7, Finset.mem_biUnion, mem_badRoots, ne_eq, sub_eq_zero, eval_sub]

#print axioms mem_B5_iff
#print axioms mem_B7_iff
#print axioms B2_card
#print axioms B3_card
#print axioms B4_card
#print axioms B5_card
#print axioms B7_card
#print axioms B2_outside
#print axioms B3_extra_outside
#print axioms B3_outside
#print axioms B4_outside
#print axioms B5_outside
#print axioms B7_outside
end
end AspisR0.Opening
