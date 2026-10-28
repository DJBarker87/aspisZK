import R0Z.SilentReduction
import R1Z.Batched

/-! J4-R1(b) (DESIGN-R1-PRIVACY-MODEL §2.4, §4; LOG D30, D33): the 47 batched
verifier relations of R1 (S2a, S2b, S1, and C_u, L_u per query) as one linear
map `relR1` on the batched cells, its kernel `B0R1`, and

* `bat_L_mem_B0R1`: for EVERY trace τ (J4′ form) whose own cells and inactive
  sum vanish, the batched cells of `L τ` satisfy every relation;
* `bat_ker_own_le_B0R1`: the batched image of own-silent mask tapes lies in
  `B0R1`.

S2b, S1 and L_u hold for every trace; S2a and C_u are the own-silent forms.
The line relation uses the inverse table `lineInverse` of BatchedAlgebra
(the normalisation Z9b found independently).  No challenge restriction. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.VerifierRelationsR1

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
open R1Z.Batched
open AspisPool.AlgorithmicCircleDecoderV7

attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
  dotLinear claimsLinear extraLinear honestClaims batchLinear

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-! ## Relations -/

inductive R1Rel
  | s2a
  | s2b
  | s1
  | circ (u : Fin 262144)
  | line (u : Fin 262144)

/-- One batched coordinate. -/
def pr (b : R1Bat) : (R1Bat → K) →ₗ[K] K := LinearMap.proj b

/-- The folded-word cells as a word on the line-18 domain. -/
def foldedWordOf : (R1Bat → K) →ₗ[K] (Fin 262144 → K) := LinearMap.funLeft K K R1Bat.folded

/-- The final cells as 64 coefficients. -/
def finalOf : (R1Bat → K) →ₗ[K] (Fin 64 → K) := LinearMap.funLeft K K R1Bat.final

/-- Parent of a query on the log-16 line. -/
def parent16 (u : Fin 262144) : Fin 65536 := ⟨u.val / 4, by omega⟩

/-- The R1 verifier relations (verifier.rs finish_relation :284-297, query
C_u :273-276, L_u :277-279; ρ batches the L_u in Rust and never enters). -/
def relR1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : (R1Bat → K) →ₗ[K] (R1Rel → K) :=
  LinearMap.pi fun r => match r with
  | .s2a => pr (.round0 0) + pr (.round0 4)
  | .s2b => pr (.round1 0) + pr (.round1 4) -
      AspisR1.RoundPairing.quarter (K := K) • ∑ i : Fin 7, ch.opening 2 ^ i.val • pr (.round0 i)
  | .s1 => ∑ i : Fin 7, ch.opening 3 ^ i.val • pr (.round1 i) -
      ∑ e : Fin 64, w2 π ch e • pr (.final e)
  | .circ u => if u ∈ ch.queries then pr (.folded u) else 0
  | .line u => if u ∈ ch.queries then
      (LinearMap.proj (parent16 u)).comp
        ((AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer 65536 (ch.opening 3)
            R1Z.BatchedAlgebra.lineInverse).comp foldedWordOf -
          (AspisR1.RepeatedLift.secondLinear (K := K)).comp finalOf)
    else 0

/-- `B0`: batched vectors satisfying all relations, as an `F`-subspace. -/
def B0R1 {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) :
    Submodule F (R1Bat → K) :=
  (LinearMap.ker (relR1 π ch)).restrictScalars F

/-! ### Evaluation of each relation -/

theorem relR1_s2a (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K) :
    relR1 π ch v .s2a = v (.round0 0) + v (.round0 4) := by
  simp only [relR1, LinearMap.pi_apply, LinearMap.add_apply, pr, LinearMap.proj_apply]

theorem relR1_s2b (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K) :
    relR1 π ch v .s2b = v (.round1 0) + v (.round1 4) -
      AspisR1.RoundPairing.quarter * ∑ i : Fin 7, ch.opening 2 ^ i.val * v (.round0 i) := by
  simp only [relR1, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, pr, LinearMap.proj_apply]

theorem relR1_s1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K) :
    relR1 π ch v .s1 = ∑ i : Fin 7, ch.opening 3 ^ i.val * v (.round1 i) -
      ∑ e : Fin 64, w2 π ch e * v (.final e) := by
  simp only [relR1, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, pr, LinearMap.proj_apply]

theorem relR1_circ (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K)
    (u : Fin 262144) (hu : u ∈ ch.queries) : relR1 π ch v (.circ u) = v (.folded u) := by
  simp only [relR1, LinearMap.pi_apply, if_pos hu, pr, LinearMap.proj_apply]

theorem relR1_circ_off (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K)
    (u : Fin 262144) (hu : u ∉ ch.queries) : relR1 π ch v (.circ u) = 0 := by
  simp only [relR1, LinearMap.pi_apply, if_neg hu, LinearMap.zero_apply]

theorem relR1_line (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K)
    (u : Fin 262144) (hu : u ∈ ch.queries) :
    relR1 π ch v (.line u) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer 65536 (ch.opening 3)
          R1Z.BatchedAlgebra.lineInverse (foldedWordOf v) (parent16 u) -
        AspisR1.RepeatedLift.secondLinear (finalOf v) (parent16 u) := by
  simp only [relR1, LinearMap.pi_apply, if_pos hu, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.proj_apply, Pi.sub_apply]

theorem relR1_line_off (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (v : R1Bat → K)
    (u : Fin 262144) (hu : u ∉ ch.queries) : relR1 π ch v (.line u) = 0 := by
  simp only [relR1, LinearMap.pi_apply, if_neg hu, LinearMap.zero_apply]

/-- A polynomial of degree at most six evaluated through its seven coefficients. -/
theorem eval_fin7 (p : Polynomial K) (hp : p.natDegree ≤ 6) (x : K) :
    p.eval x = ∑ i : Fin 7, x ^ i.val * p.coeff i.val := by
  rw [Polynomial.eval_eq_sum_range' (p := p) (n := 7) (by omega) x, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## The relations on the honest batched read -/

/-- S2b holds for every trace. -/
theorem read_s2b (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (τ : Trace K) :
    relR1 π ch (BatchedLayer.read (Bat := R1Bat) π ch τ) .s2b = 0 := by
  rw [relR1_s2b, read_round1, read_round1]
  simp only [read_round0]
  rw [← eval_fin7 _ (AspisR1.RoundPairing.round_degree (n := 256) (batchR1 π ch τ)
    (weightsR1 π ch))]
  have h : (AspisR1.RoundPairing.roundPolynomial (n := 64) (q1 π ch τ) (w1 π ch)).coeff
        (0 : Fin 7).val +
      (AspisR1.RoundPairing.roundPolynomial (n := 64) (q1 π ch τ) (w1 π ch)).coeff
        (4 : Fin 7).val =
      AspisR1.RoundPairing.quarter *
        (AspisR1.RoundPairing.roundPolynomial (n := 256) (batchR1 π ch τ)
          (weightsR1 π ch)).eval (ch.opening 2) :=
    R1Z.BatchedAlgebra.s2b_identity (ch.opening 2) (batchR1 π ch τ) (weightsR1 π ch)
  rw [h, sub_self]

/-- S1 holds for every trace. -/
theorem read_s1 (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (τ : Trace K) :
    relR1 π ch (BatchedLayer.read (Bat := R1Bat) π ch τ) .s1 = 0 := by
  rw [relR1_s1]
  simp only [read_round1, read_final]
  rw [← eval_fin7 _ (AspisR1.RoundPairing.round_degree (n := 64) (q1 π ch τ) (w1 π ch))]
  have h : (AspisR1.RoundPairing.roundPolynomial (n := 64) (q1 π ch τ) (w1 π ch)).eval
        (ch.opening 3) =
      ∑ e : Fin 64,
        AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 (ch.opening 3)
            (q1 π ch τ) e *
          AspisR1.RoundPairing.dualFold (n := 64) (ch.opening 3) (w1 π ch) e :=
    R1Z.BatchedAlgebra.s1_identity (ch.opening 3) (q1 π ch τ) (w1 π ch)
  rw [h, sub_eq_zero]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/-- L_u holds for every trace (line_identity on the α₀-folded coefficients). -/
theorem read_line (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (τ : Trace K)
    (u : Fin 262144) : relR1 π ch (BatchedLayer.read (Bat := R1Bat) π ch τ) (.line u) = 0 := by
  by_cases hu : u ∈ ch.queries
  · rw [relR1_line _ _ _ _ hu, sub_eq_zero,
      AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer_apply]
    have hc (s : Fin 4) :
        foldedWordOf (BatchedLayer.read (Bat := R1Bat) π ch τ)
            (AspisV5ComponentCConcreteFoldLinearity.childIndex (parent16 u) s) =
          AspisWide.FinalEncoder.exactFinalLinear (q1 π ch τ)
            (AspisV5ComponentCConcreteFoldLinearity.childIndex (parent16 u) s) := by
      have hopen : FoldedOpen ch
          (AspisV5ComponentCConcreteFoldLinearity.childIndex (parent16 u) s) := by
        refine ⟨u, hu, ?_⟩
        have hs := s.isLt
        simp only [AspisV5ComponentCConcreteFoldLinearity.childIndex_val, parent16]
        omega
      exact read_folded π ch τ _ hopen
    have hf : finalOf (BatchedLayer.read (Bat := R1Bat) π ch τ) =
        AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 (ch.opening 3)
          (q1 π ch τ) := by
      funext e
      exact read_final π ch τ e
    simp only [hc]
    rw [hf]
    exact R1Z.BatchedAlgebra.line_identity (ch.opening 3) (q1 π ch τ) (parent16 u)
  · exact relR1_line_off _ _ _ _ hu

/-! ## Own-silent traces: S2a and C_u -/

section OwnSilent

variable {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
  (τ : Trace K)

/-- S2a on a trace whose own claim/extra/OOD cells and inactive sum vanish. -/
theorem read_s2a
    (hclaim : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.pointClaim j c) = 0)
    (hextra : ∀ c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.extraClaim c) = 0)
    (hood : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.ood j c) = 0)
    (hia : R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ .inactiveSum = 0) :
    relR1 π ch (BatchedLayer.read (Bat := R1Bat) π ch τ) .s2a = 0 := by
  have z0 : ell π ch 0 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_inactive]
    exact (R0Z.SilentReduction.linearPayload_inactiveSum (Bat := R1Bat) π ch τ).symm.trans hia
  have z1 : ell π ch 1 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_claim0]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show claimsLinear (alpha ch) 0 c τ = 0 from hclaim 0 c, mul_zero]
  have z2 : ell π ch 2 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_claim1]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show claimsLinear (alpha ch) 1 c τ = 0 from hclaim 1 c, mul_zero]
  have z3 : ell π ch 3 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_claim2]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show claimsLinear (alpha ch) 2 c τ = 0 from hclaim 2 c, mul_zero]
  have z4 : ell π ch 4 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_extra]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show extraLinear π (alpha ch) c τ = 0 from hextra c, mul_zero]
  have z5 : ell π ch 5 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_ood0]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show oodLinear (ch.circle 0) (coeffsLinear π (τ c)) = 0 from hood 0 c, mul_zero]
  have z6 : ell π ch 6 (batchR1 π ch τ) = 0 := by
    rw [ell_batch_ood1]
    exact Finset.sum_eq_zero fun c _ => by
      rw [show oodLinear (ch.circle 1) (coeffsLinear π (τ c)) = 0 from hood 1 c, mul_zero]
  rw [relR1_s2a, read_round0, read_round0]
  have h : (AspisR1.RoundPairing.roundPolynomial (n := 256) (batchR1 π ch τ)
          (weightsR1 π ch)).coeff (0 : Fin 7).val +
        (AspisR1.RoundPairing.roundPolynomial (n := 256) (batchR1 π ch τ)
          (weightsR1 π ch)).coeff (4 : Fin 7).val =
      AspisR1.RoundPairing.quarter *
        ∑ k : Fin 7, ch.opening 1 ^ k.val * ell π ch k (batchR1 π ch τ) :=
    R1Z.BatchedAlgebra.s2a_identity (ch.opening 1) (ell π ch) (batchR1 π ch τ)
  rw [h, Fin.sum_univ_seven, z0, z1, z2, z3, z4, z5, z6]
  simp only [mul_zero, add_zero]

/-- C_u on a trace whose opened symbols vanish. -/
theorem read_circ
    (hopen : ∀ q s c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.opened q s c) = 0)
    (u : Fin 262144) :
    relR1 π ch (BatchedLayer.read (Bat := R1Bat) π ch τ) (.circ u) = 0 := by
  by_cases hu : u ∈ ch.queries
  · rw [relR1_circ _ _ _ _ hu, read_folded π ch τ u ⟨u, hu, rfl⟩]
    have hop (s : Fin 4) (c : Fin 29) :
        AspisWide.Agreement.exactInitialLinear (coeffsLinear π (τ c))
          (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) = 0 := by
      have h := hopen u s c
      rw [show R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.opened u s c) =
        linearPayload (Bat := R1Bat) π ch τ (.opened u s c) from rfl] at h
      simp only [linearPayload, LinearMap.pi_apply, if_pos hu, LinearMap.comp_apply,
        LinearMap.proj_apply] at h
      exact h
    have hfib : AspisR1.FirstFold.fibre
        (AspisWide.InitialEncoder.exactInitialEncoder (batchR1 π ch τ)) u = 0 := by
      funext s
      have e : AspisWide.InitialEncoder.exactInitialEncoder (batchR1 π ch τ)
            (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) =
          ∑ c : Fin 29, ch.opening 0 ^ c.val *
            AspisWide.Agreement.exactInitialLinear (coeffsLinear π (τ c))
              (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) :=
        map_batchR1 π ch ((LinearMap.proj
          (AspisV5ComponentCConcreteFoldLinearity.childIndex u s)).comp
            AspisWide.Agreement.exactInitialLinear) τ
      show AspisWide.InitialEncoder.exactInitialEncoder (batchR1 π ch τ)
          (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) = 0
      rw [e]
      exact Finset.sum_eq_zero fun c _ => by rw [hop s c, mul_zero]
    exact R1Z.BatchedAlgebra.circ_zero_of_fibre_zero (ch.opening 2) (batchR1 π ch τ) u hfib
  · exact relR1_circ_off _ _ _ _ hu

/-- J4′ form: for every trace whose own cells (claims, extra claims, OOD,
opened symbols) and inactive sum vanish, the batched cells of `L τ` satisfy
every R1 relation. -/
theorem bat_L_mem_B0R1
    (hclaim : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.pointClaim j c) = 0)
    (hextra : ∀ c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.extraClaim c) = 0)
    (hood : ∀ j c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.ood j c) = 0)
    (hopen : ∀ q s c, R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ (.opened q s c) = 0)
    (hia : R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ .inactiveSum = 0) :
    R0Z.SilentReduction.batRead (F := F) (Bat := R1Bat)
        (R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ) ∈ B0R1 (F := F) π ch := by
  have hb : R0Z.SilentReduction.batRead (F := F) (Bat := R1Bat)
      (R0Z.PayloadSplit.L (Bat := R1Bat) π B ch τ) =
        BatchedLayer.read (Bat := R1Bat) π ch τ := by
    funext b
    rfl
  rw [hb, B0R1, Submodule.restrictScalars_mem, LinearMap.mem_ker]
  funext r
  cases r with
  | s2a => exact read_s2a π B ch τ hclaim hextra hood hia
  | s2b => exact read_s2b π ch τ
  | s1 => exact read_s1 π ch τ
  | circ u => exact read_circ π B ch τ hopen u
  | line u => exact read_line π ch τ u

end OwnSilent

/-- Corollary for mask tapes: the batched image of own-silent tapes lies in
`B0R1` (`ia_pure_zero` supplies the inactive sum). -/
theorem bat_ker_own_le_B0R1 {F : Subfield K} (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) :
    (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch)).map
        (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch) ≤ B0R1 (F := F) π ch := by
  rintro _ ⟨m, hm, rfl⟩
  have hA : (A (Bat := R1Bat) π B ch).comp inlM m =
      R0Z.PayloadSplit.L (Bat := R1Bat) π B ch (pureTrace B m) :=
    R0Z.PureRounds.A_pure π B ch m
  have hown : ∀ cell, R0Z.SilentReduction.ownProj (F := F) (Bat := R1Bat)
      (R0Z.PayloadSplit.L (Bat := R1Bat) π B ch (pureTrace B m)) cell = 0 := by
    intro cell
    have h := congrFun (LinearMap.mem_ker.1 hm) cell
    rw [R0Z.SilentReduction.ownMap, LinearMap.comp_apply, hA] at h
    exact h
  have hia : R0Z.PayloadSplit.L (Bat := R1Bat) π B ch (pureTrace B m) .inactiveSum = 0 := by
    have h := R0Z.SilentReduction.ia_pure_zero (Bat := R1Bat) π B ch m
    rw [hA] at h
    exact h
  have hmb : R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m =
      R0Z.SilentReduction.batRead (F := F) (Bat := R1Bat)
        (R0Z.PayloadSplit.L (Bat := R1Bat) π B ch (pureTrace B m)) := by
    rw [R0Z.SilentReduction.batMap, LinearMap.comp_apply, hA]
  rw [hmb]
  exact bat_L_mem_B0R1 π B ch (pureTrace B m)
    (fun j c => hown (.pointClaim j c)) (fun c => hown (.extraClaim c))
    (fun j c => hown (.ood j c)) (fun q s c => hown (.opened q s c)) hia

#print axioms relR1_s2a
#print axioms relR1_s2b
#print axioms relR1_s1
#print axioms relR1_circ
#print axioms relR1_line
#print axioms eval_fin7
#print axioms read_s2b
#print axioms read_s1
#print axioms read_line
#print axioms read_s2a
#print axioms read_circ
#print axioms bat_L_mem_B0R1
#print axioms bat_ker_own_le_B0R1

end R1Z.VerifierRelationsR1

end
