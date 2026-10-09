import R0P.MaskEarly
import R0P.MaskNoHit

/-! The complete 32-round masked D3 bridge, generic over maskPoly of degree 27. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial R0P.Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
open AspisR0.Chord AspisR0.ChordGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]


theorem accepted_no_hit_extractedZ (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31-1) {Sfield : Fin 29 → Subfield K}
    (fallback1 : Point K) (maskPoly : (Fin 10 → K) → K) (hMask : MaskDegree maskPoly)
    (B : PackBasis (Sfield 0))
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K)) (m : MsgZ K)
    (hdec : decisionZ maskPoly B P m = true)
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskPoly B) P.statement [] P.rounds)
    (hfirst : ∀ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)),
      openingViewZ P = some Q → ∀ (y : Fin 29 → Fin 2 → K) (γ : K),
        Q.rounds.head? = some (.values y, .field γ) → γ ≠ 0) :
    ∃ t : Trace K, InputNoteExtracted P.statement.pub t := by
  unfold decisionZ at hdec
  obtain ⟨Q,cs,hcs,polys,claim,om,hview,hparse,hpolys,hclaim,hsum,_hm,hodec,hcard⟩ :=
    of_decide_eq_true hdec
  have hnogood : ¬ R0FS.good Q.statement Q.rounds := by
    intro hg
    exact hno (openingZ_good_hitFrom (sourceDataWithFallbackZ fallback1 maskPoly B)
      rfl rfl P Q hview hg)
  obtain ⟨t,ht⟩ := opening_decision_witness Q om hodec hcard hnogood (hfirst Q hview)
  obtain ⟨sem,cs',hw,gw,y,y0,z0,z1,hcs',hb,hne,h0,h1,os,hsem,hparse',hc2,hrounds,hQ⟩ :=
    openingViewZ_some_structure P Q hview
  have htake : P.rounds.take 25 = sem := by
    rw [hrounds, ← hsem]
    exact List.take_left
  rw [htake] at hparse hpolys
  have heq : cs' = cs := Option.some.inj (hparse'.symm.trans hparse)
  subst cs'
  have hclaimsem : claimOf sem = some claim := by
    rw [← htake, claimOf_take P.rounds 25 (by omega)]
    exact hclaim
  subst Q
  let pre : Fin 14 → K := fun j => cs.getD j.val 0
  let alpha : Fin 10 → K := fun j => cs.getD (15+j.val) 0
  let r : Fin 24 → K := fun j => cs.getD j.val 0
  have hα : (fun j : Fin 10 => cs[15+j.val]'(by omega)) = alpha := by
    funext j
    simp only [alpha, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 15+j.val < cs.length by omega), Option.getD_some]
  have hy : y = honestClaims t alpha := by
    funext j l
    have h := ht.2.1 j l
    change y j l = AspisR0.LinearDual.dot
      (AspisR0.Opening.eqWeight (openingPoints (fun j => cs[15+j.val]'(by omega)) j)) (t l) at h
    simpa only [honestClaims,hα] using h
  have hpre : (fun j : Fin 14 => cs[j.val]'(by omega)) = pre := by
    funext j
    simp only [pre, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j.val < cs.length by omega), Option.getD_some]
  have heta14 : (cs[14]'(by omega)) = cs.getD 14 0 := by
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 14 < cs.length by omega), Option.getD_some]
  have hsum' : sumcheckChecksZ maskPoly P.statement.pub B pre (cs.getD 14 0) claim alpha polys
      (honestClaims t alpha) := by
    simpa only [openingStmt,hy,hpre,heta14,hα] using hsum
  have hn : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskPoly B) P.statement []
      (sem ++ ((Msg.beforeZ0 y,Chal.circle z0) :: (Msg.beforeZ1 y0,Chal.circle z1) :: openingPairsZ os)) := by
    simpa only [hrounds] using hno
  have heta := no_hit_eta fallback1 maskPoly B P.statement sem _ hsem cs hparse claim hclaimsem
    hw gw hc2 t ht.1 hn
  have halpha := no_hit_alpha fallback1 maskPoly B P.statement sem _ hsem cs hparse claim hclaimsem
    polys hpolys hsum'.1 hw gw hc2 t ht.1 hn
  have htotal := originalTotal_zero_of_masked_accept maskPoly hMask P.statement.pub B t pre
    (cs.getD 14 0) claim alpha polys (checksAcceptZ maskPoly P.statement.pub B t pre
      (cs.getD 14 0) claim alpha polys hsum') halpha heta
  have hearly := no_hit_early fallback1 maskPoly B P.statement sem _ hsem cs hparse hw gw hc2 t ht.1 hn
  obtain ⟨hlc,hth,hzc,hmu⟩ := earlyRounds_cover t P.statement.pub B r hearly
  have hzcpre : semSlice r 3 10 = preZc pre := by
    funext j
    simp only [semSlice,semPrefixVal,dif_pos (show 3+j.val < 24 by omega)]
    rfl
  rw [hzcpre] at hzc hmu
  have hA := witness_baseTyped P.statement _ t ht
  have hprod := semantic_of_total_zero prime hprime P.statement.F (contextBasis P.statement B)
    P.statement.pub t hA P.statement.pubBase pre htotal hlc hth hzc hmu
  exact ⟨t, semantic_extraction P.statement.pub t (r 0) (r 1) hprod
    (extraction_step P.statement.pub (r 0) (r 1) t)⟩

#print axioms accepted_no_hit_extractedZ
end
end R0P.Mask
