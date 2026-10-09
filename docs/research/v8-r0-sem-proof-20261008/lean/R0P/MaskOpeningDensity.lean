import R0P.MaskD2Glue

/-! Duplex transfer of masked semantic/circle/opening root bounds. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 FS2.Duplex R0C.SemStatement R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8PairedCommitment
open AspisR0.ChordGeometry R0C.SlackStatement AspisWideTower
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact} {L : Nat}
variable (maskClaims : (Fin 29 → WideExact) → (Fin 29 → WideExact) → (Fin 10 → WideExact) → WideExact) (B : PackBasis F) (budget : Nat → ℚ)



theorem late_roundBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : ChalZ WideExact) (hi : 27 ≤ Q.round)
    (h : roundBad (sourceDataZ maskClaims B) Q m c) :
    ∃ O om oc, openingViewZ Q = some O ∧ m = .opening om ∧ c = .opening oc ∧
      Q.round = 27 + O.round ∧ R0FS.roundBad O.statement O.rounds om oc := by
  simp only [roundBad, sourceDataZ, sourceDataWithFallbackZ] at h
  rcases h with hs | hz0 | hz1 | ho
  · obtain ⟨_,_,hlt,_,_,_⟩ := hs; omega
  · obtain ⟨_,_,he,_,_,_⟩ := hz0; omega
  · obtain ⟨_,_,_,_,he,_,_,_,_⟩ := hz1; omega
  · exact ho

theorem opening_fieldZ_D2 (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (j : Fin 4) (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T' T : Table (Addr L) State)
    (hr : P.round = 27 + j.val) (hd : (duplexRowsZ maskClaims B budget).doomed P T')
    (hσ : ∀ a, p.σ (27 + j.val) a = .opening (R0C.V3.DQ.σQ j.val a)) :
    independentMean (Duplex.samp p (27 + j.val) P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤
      epsilonSlack WideExact delta0 j.val := by
  let Q := valuePrefix P
  have hQr : Q.round = 27 + j.val := (valuePrefix_round P).trans hr
  by_cases hp : ∃ O om, openingViewZ Q = some O ∧ m = .opening om ∧ O.round = j.val
  · obtain ⟨O,om,hview,rfl,hlen⟩ := hp
    apply one_row_bound maskClaims B budget p (27 + j.val) P (.opening om) T
      (fun a => R0FS.roundBad O.statement O.rounds om (R0C.V3.DQ.σQ j.val a)) _
    · intro a b hf
      obtain ⟨O',om',oc,hview',hm,hc,_,hb⟩ := late_roundBadZ maskClaims B Q (.opening om)
        (p.σ (27 + j.val) a) (by omega)
        (flipZ maskClaims B budget P (.opening om) (p.σ (27+j.val) a,b) T' T hd hf)
      have hO : O' = O := Option.some.inj (hview'.symm.trans hview)
      have hom : om' = om := (Msg.opening.inj hm).symm
      subst O'; subst om'
      rw [hσ a] at hc
      rw [Chal.opening.inj hc]
      exact hb
    · exact R0C.V3.DQ.round_field_bound O.statement O.rounds om j.val j.isLt hlen
  · apply one_row_bound maskClaims B budget p (27+j.val) P m T (fun _ => False) _
    · intro a b hf
      obtain ⟨O,om,oc,hview,hm,_,hlen,_⟩ := late_roundBadZ maskClaims B Q m
        (p.σ (27+j.val) a) (by omega)
        (flipZ maskClaims B budget P m (p.σ (27+j.val) a,b) T' T hd hf)
      exact hp ⟨O,om,hview,hm,by omega⟩
    · simp only [indicator_false, mean_const]
      exact R0C.SlackDensity.epsilonSlack_nonneg R0C.ConcreteSlack.delta0_nonneg j.val

#print axioms late_roundBadZ
#print axioms opening_fieldZ_D2

private theorem independentMean_zero_of_pointwise_zero
    {I A O : Type} [Fintype A] (p : Program I A O)
    (f : View I A O → ℚ) (hf : ∀ w, f w = 0) : independentMean p f = 0 := by
  induction p generalizing f with
  | done o => exact hf ([], o)
  | ask i next ih =>
      simp only [independentMean]
      calc
        _ = mean (fun _ : A => (0 : ℚ)) := by
          apply mean_congr
          intro a
          exact ih a _ (fun w => hf ((i, a) :: w.1, w.2))
        _ = 0 := by simp only [mean, Finset.sum_const_zero, zero_div]

theorem opening_q22Z_D2 (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T' T : Table (Addr L) State)
    (hr : P.round = 31) (hd : (duplexRowsZ maskClaims B budget).doomed P T') :
    independentMean (combinedSamplerAt 31 p 31 P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤
      epsilonSlack WideExact delta0 4 := by
  let Q := valuePrefix P
  have hQr : Q.round = 31 := (valuePrefix_round P).trans hr
  by_cases hp : ∃ O om, openingViewZ Q = some O ∧ m = .opening om ∧ O.round = 4
  · obtain ⟨O,om,hview,rfl,hlen⟩ := hp
    have hpoint (s' : State) (bs xs : List State) :
        ¬ (duplexRowsZ maskClaims B budget).doomed
          (P.ext (.opening om) (openingChallenge (R0C.V3.DQ.out4 s' bs xs))) T →
        R0FS.roundBad O.statement O.rounds om (R0C.V3.DQ.out4 s' bs xs).1 := by
      intro hf
      obtain ⟨O',om',oc,hview',hm,hc,_,hb⟩ := late_roundBadZ maskClaims B Q (.opening om)
        (openingChallenge (R0C.V3.DQ.out4 s' bs xs)).1 (by omega)
        (flipZ maskClaims B budget P (.opening om)
          (openingChallenge (R0C.V3.DQ.out4 s' bs xs)) T' T hd hf)
      have hO : O' = O := Option.some.inj (hview'.symm.trans hview)
      have hom : om' = om := (Msg.opening.inj hm).symm
      subst O'; subst om'
      rw [Chal.opening.inj hc]
      exact hb
    rw [combinedSamplerAt, if_neg (show ¬ (31 : Nat) < 31 by omega)]
    simp only [FS2.Sampler.toProgram, independentMean]
    calc
      mean (fun s' : State => independentMean
        (R0C.V3.DQ.chainS (openingParamsAt 27 p s')
          (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []).toProgram
        (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed
          (P.ext (.opening om) w.2) T)))
          ≤ mean (fun _ : State => epsilonSlack WideExact delta0 4) := by
        apply mean_mono
        intro s'
        rw [chainS_independentMean (openingParamsAt 27 p s')
          (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs))
          (fun c => indicator (¬ (duplexRowsZ maskClaims B budget).doomed
            (P.ext (.opening om) c) T)) 8 s' [] []]
        simp only [List.nil_append]
        apply le_trans _ (R0C.V3.DQ.round_q22_bound O.statement O.rounds om hlen s')
        apply R0C.V3.Q22.chainE_mono
        intro bs xs
        exact indicator_mono (hpoint s' bs xs)
      _ = epsilonSlack WideExact delta0 4 := mean_const _
  · rw [independentMean_zero_of_pointwise_zero _ _ (by
      intro w
      apply (indicator_iff (iff_false_intro ?_)).trans indicator_false
      intro hf
      obtain ⟨O,om,oc,hview,hm,_,hlen,_⟩ := late_roundBadZ maskClaims B Q m w.2.1 (by omega)
        (flipZ maskClaims B budget P m w.2 T' T hd hf)
      exact hp ⟨O,om,hview,hm,by omega⟩)]
    exact R0C.SlackDensity.epsilonSlack_nonneg R0C.ConcreteSlack.delta0_nonneg 4

#print axioms opening_q22Z_D2

end
end R0P.Mask
