import R0P.MaskEarly
import R0P.MaskNoHit

/-! The complete 32-round masked D3 bridge, generic over maskClaims of degree 27. -/
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
    (fallback1 : Point K) (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K) (hMask : MaskDegree maskClaims)
    (B : PackBasis (Sfield 0))
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K)) (m : MsgZ K)
    (hdec : decisionZ maskClaims B P m = true)
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B) P.statement [] P.rounds)
    (hfirst : ∀ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)),
      openingViewZ P = some Q → ∀ (y : Fin 29 → Fin 2 → K) (γ : K),
        Q.rounds.head? = some (.values y, .field γ) → γ ≠ 0) :
    ∃ t : Trace K, InputNoteExtracted P.statement.pub t := by
  unfold decisionZ at hdec
  obtain ⟨Q,cs,hcs,polys,claim,om,hview,hparse,hpolys,hclaim,hsum,_hm,hodec,hcard⟩ :=
    of_decide_eq_true hdec
  have hnogood : ¬ R0FS.good Q.statement Q.rounds := by
    intro hg
    exact hno (openingZ_good_hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B)
      rfl rfl P Q hview hg)
  obtain ⟨mcoeff, hmcoeff⟩ := opening_decision_witness Q om hodec hcard hnogood (hfirst Q hview)
  let t := rowsOf P.statement.transport mcoeff
  have ht : R0FS.Witness Q.statement (coeffsOf P.statement.transport t) := by
    simpa only [t, coeffsOf_rowsOf] using hmcoeff
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
    change y j l = AspisR0.RoundNormalization.dot
      (AspisR0.Opening.coeffWeight P.statement.transport
        (AspisR0.Opening.eqWeight (openingPoints (fun j => cs[15+j.val]'(by omega)) j)))
      (coeffsOf P.statement.transport t l) at h
    rw [dot_coeffWeight_coeffsOf] at h
    simpa only [honestClaims, hα, AspisR0.RoundNormalization.dot, AspisR0.LinearDual.dot] using h
  have hyx : P.statement.extraClaims = honestExtra P.statement.transport t alpha := by
    funext l
    have h := ht.2.2.1 l
    simpa only [openingStmt, honestExtra, libraWeight, hα] using h
  have hpre : (fun j : Fin 14 => cs[j.val]'(by omega)) = pre := by
    funext j
    simp only [pre, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j.val < cs.length by omega), Option.getD_some]
  have heta14 : (cs[14]'(by omega)) = cs.getD 14 0 := by
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 14 < cs.length by omega), Option.getD_some]
  have hsum' : sumcheckChecksZ maskClaims P.statement.pub B pre (cs.getD 14 0) claim alpha polys
      (honestClaims t alpha) (honestExtra P.statement.transport t alpha) := by
    simpa only [openingStmt,hy,hyx,hpre,heta14,hα] using hsum
  have hn : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B) P.statement []
      (sem ++ ((Msg.beforeZ0 y,Chal.circle z0) :: (Msg.beforeZ1 y0,Chal.circle z1) :: openingPairsZ os)) := by
    simpa only [hrounds] using hno
  have heta := no_hit_eta fallback1 maskClaims B P.statement sem _ hsem cs hparse claim hclaimsem
    hw gw hc2 t ((mem_LambdaRows _ _ _).mpr ht.1) hn
  have halpha := no_hit_alpha fallback1 maskClaims B P.statement sem _ hsem cs hparse claim hclaimsem
    polys hpolys hsum'.1 hw gw hc2 t ((mem_LambdaRows _ _ _).mpr ht.1) hn
  have htotal := originalTotal_zero_of_masked_accept maskClaims hMask P.statement.transport P.statement.pub B t pre
    (cs.getD 14 0) claim alpha polys (checksAcceptZ maskClaims P.statement.transport P.statement.pub B t pre
      (cs.getD 14 0) claim alpha polys hsum') halpha heta
  have hearly := no_hit_early fallback1 maskClaims B P.statement sem _ hsem cs hparse hw gw hc2 t ((mem_LambdaRows _ _ _).mpr ht.1) hn
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

namespace R0P.Mask
open FS FS2 FS2.Duplex R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement
open AspisWideTower AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
noncomputable section
attribute [local instance] Classical.propDecidable

theorem d3Z (prime : Nat) [CharP WideExact prime] (hprime : prime = 2^31-1)
    {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
    (maskClaims : (Fin 29 → WideExact) → (Fin 29 → WideExact) → (Fin 10 → WideExact) → WideExact) (hMask : MaskDegree maskClaims)
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (msg : Pf → Nat → MsgZ WideExact)
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext WideExact Sfield) (MsgZ WideExact)
        (Duplex.Chal (ChalZ WideExact)) × MsgZ WideExact ×
          Duplex.Chal (ChalZ WideExact))))
    (budget : Nat → ℚ)
    (hσ27 : ∀ s, p.σ 27 s = .opening (R0C.V3.DQ.σQ 0 s)) :
    FS2.D3 (combinedProtocolZ B p msg decode) (duplexRowsZ maskClaims B budget)
      (FS2.verifier (combinedProtocolZ B p msg decode) (combinedDecisionZ maskClaims B)) := by
  intro H x π T hd
  rw [FS2.verifier_eval]
  by_contra hfalse
  have hdec : combinedDecisionZ maskClaims B
      ((combinedProtocolZ B p msg decode).transcript H x π 32) (msg π 32) = true := by
    exact R0C.V3.DQ.bool_true_of_ne_false hfalse
  let P := valuePrefix ((combinedProtocolZ B p msg decode).transcript H x π 32)
  have hd' : (¬ ∃ t, InputNoteExtracted P.statement.pub t) ∧
      ¬ hitFrom (sourceDataZ maskClaims B) P.statement [] P.rounds := hd
  obtain ⟨t, ht⟩ := accepted_no_hit_extractedZ prime hprime circleFallback1 maskClaims hMask B P
    (msg π 32) hdec hd'.2 (by
      intro Q hview y γ hhead
      have hparsed := opening_head_at_27 P Q hview
      simp only [hhead, Option.map_some] at hparsed
      have hactual := transcript_value_getElem (combinedProtocolZ B p msg decode) H x π 32 27 (by omega)
      have hc := congrArg Prod.snd (Option.some.inj (hparsed.symm.trans hactual))
      obtain ⟨a, ha⟩ := combined_chal27 B p msg decode hσ27 H x π
      rw [ha] at hc
      have hγ : γ = R0C.ModuloField.gamma a := R0FS.Chal.field.inj (Chal.opening.inj hc)
      rw [hγ]
      exact R0C.ModuloField.gamma_ne_zero a)
  exact hd'.1 ⟨t, ht⟩


#print axioms d3Z
end
end R0P.Mask
