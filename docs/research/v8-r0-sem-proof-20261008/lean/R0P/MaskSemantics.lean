import R0P.MaskD2

/-! Masked semantic core. Sumcheck first identifies the masked Boolean sum;
the eta exclusion then recovers the original zero-sum claim. The remaining
zerocheck, lane and LogUp consequences are the ones used by SemD3.d3_core. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.Sumcheck Polynomial
noncomputable section
variable {K : Type} [Field K]

/-- Honest Boolean rows include the mask's literal Boolean-row value. -/
theorem honestRowsZ (maskClaims : (Fin 29 → K) → (Fin 10 → K) → K) (pub : Public K)
    {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta : K) (b : Fin 10 → Bool) :
    virtualPolyZ maskClaims pub B t pre eta (ofBool b) = maskClaims (fun l => honestClaims t (ofBool b) 0 l) (ofBool b) + eta *
      (eqwB 10 (preZc pre) b * lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B) b +
        pre 13 * t 26 (rowOf b) + (pre 13)^2 *
          ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) := by
  unfold virtualPolyZ
  rw [honestRows pub B t pre b]

/-- The masked boundary, chain and terminal checks give recursive acceptance. -/
theorem checksAcceptZ (maskClaims : (Fin 29 → K) → (Fin 10 → K) → K) (pub : Public K)
    {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta claim : K) (alpha : Fin 10 → K)
    (polys : Fin 10 → K[X])
    (h : sumcheckChecksZ maskClaims pub B pre eta claim alpha polys (honestClaims t alpha)) :
    accept 27 10 (virtualPolyZ maskClaims pub B t pre eta) claim polys alpha := by
  exact accept_of_checks 27 9 _ claim polys alpha h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Neither the eta argument nor its zero-slope branch requires a property
of maskClaims. Its degree bound is used only by sumcheck soundness. -/
theorem originalTotal_zero_of_masked_accept (maskClaims : (Fin 29 → K) → (Fin 10 → K) → K)
    (hMask : MaskDegree maskClaims) (pub : Public K) {F : Subfield K}
    (B : PackBasis F) (t : Trace K) (pre : Fin 14 → K) (eta claim : K)
    (alpha : Fin 10 → K) (polys : Fin 10 → K[X])
    (hacc : accept 27 10 (virtualPolyZ maskClaims pub B t pre eta) claim polys alpha)
    (hAlpha : ¬ badAlpha 27 10 (virtualPolyZ maskClaims pub B t pre eta) polys alpha)
    (hEta : ¬ etaBad claim (maskTotal maskClaims t) (originalTotal pub B t pre) eta) :
    originalTotal pub B t pre = 0 := by
  have hsum : bsum 10 (virtualPolyZ maskClaims pub B t pre eta) = claim := by
    by_contra hne
    exact hAlpha (sound 27 10 _ claim polys alpha
      (virtualPolyZ_indDeg maskClaims hMask pub B t pre eta) hacc hne)
  rw [bsum_eq_bsumB, virtualPolyZ_total] at hsum
  by_contra hs
  exact hEta ⟨hs, hsum.symm⟩

/-- The part of the original semantic core after sumcheck: a zero Boolean
sum outside the four early bad families implies production and link balance. -/
theorem semantic_of_total_zero (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31-1) (F : Subfield K) (B : PackBasis F)
    (pub : Public K) (t : Trace K) (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (pre : Fin 14 → K)
    (hTotal : originalTotal pub B t pre = 0)
    (hlc : ¬ BadLogUp pub t (pre 0) (pre 1))
    (hTheta : ¬ BadTheta (laneOf t pub (pre 0) (pre 1) B) (pre 2))
    (hZc : ¬ BadZc (lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B)) (preZc pre))
    (hMu : ¬ BadMu
      (mle 10 (lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B)) (preZc pre))
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) (pre 13)) :
    ProductionHolds pub (pre 0) (pre 1) t ∧ CopyLinkBalance pub t := by
  have he : (fun b => virtualPoly pub B t pre (ofBool b)) = fun b =>
      (eqwB 10 (preZc pre) b * lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B) b +
        pre 13 * t 26 (rowOf b)) + (pre 13)^2 *
        ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) := by
    funext b
    exact honestRows pub B t pre b
  unfold originalTotal at hTotal
  rw [he, bsumB_add, bsumB_add, bsumB_eqw, bsumB_smul, bsumB_smul] at hTotal
  have h3 : mle 10 (lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B)) (preZc pre) = 0 ∧
      bsumB 10 (fun b => t 26 (rowOf b)) = 0 ∧
      bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) = 0 := by
    by_contra hc
    apply hMu
    exact ⟨by tauto, hTotal⟩
  obtain ⟨hm, h1, h2⟩ := h3
  have hcomp : ∀ b, lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B) b = 0 := by
    by_contra hc
    push Not at hc
    exact hZc ⟨hc, hm⟩
  have hlanes : ∀ i b, laneOf t pub (pre 0) (pre 1) B i b = 0 := by
    by_contra hc
    push Not at hc
    exact hTheta ⟨hc, hcomp⟩
  have hprod : ProductionHolds pub (pre 0) (pre 1) t :=
    (lanes_zero_iff_holds F B pub (pre 0) (pre 1) t hA hpub).mp hlanes
  have hlogup : LogUpStep pub t (BadLogUp pub t) (fun b => t 26 (rowOf b))
      (fun b => (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) :=
    logup_step_of pub t (fun lam chi => logupL1 pub t lam chi)
      (fun lam chi => logupL2 pub t lam chi) (fun lam chi => logupL3 pub t lam chi)
      (fun lam => logupL4 prime hprime pub t lam) (logupL5 prime hprime pub t) _ _
      (lane_h1_sum t) (lane_inactive_sum t)
  exact ⟨hprod, hlogup (pre 0) (pre 1) hlc hprod.2.2.2.2.2.2.2 h1 h2⟩

#print axioms honestRowsZ
#print axioms checksAcceptZ
#print axioms originalTotal_zero_of_masked_accept
#print axioms semantic_of_total_zero
end
end R0P.Mask
