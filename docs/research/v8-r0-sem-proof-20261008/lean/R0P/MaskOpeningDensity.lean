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
variable (maskPoly : (Fin 10 → WideExact) → WideExact) (B : PackBasis F) (budget : Nat → ℚ)



theorem late_roundBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : ChalZ WideExact) (hi : 27 ≤ Q.round)
    (h : roundBad (sourceDataZ maskPoly B) Q m c) :
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
    (hr : P.round = 27 + j.val) (hd : (duplexRowsZ maskPoly B budget).doomed P T')
    (hσ : ∀ a, p.σ (27 + j.val) a = .opening (R0C.V3.DQ.σQ j.val a)) :
    independentMean (Duplex.samp p (27 + j.val) P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskPoly B budget).doomed (P.ext m w.2) T)) ≤
      epsilonSlack WideExact delta0 j.val := by
  let Q := valuePrefix P
  have hQr : Q.round = 27 + j.val := (valuePrefix_round P).trans hr
  by_cases hp : ∃ O om, openingViewZ Q = some O ∧ m = .opening om ∧ O.round = j.val
  · obtain ⟨O,om,hview,rfl,hlen⟩ := hp
    apply one_row_bound maskPoly B budget p (27 + j.val) P (.opening om) T
      (fun a => R0FS.roundBad O.statement O.rounds om (R0C.V3.DQ.σQ j.val a)) _
    · intro a b hf
      obtain ⟨O',om',oc,hview',hm,hc,_,hb⟩ := late_roundBadZ maskPoly B Q (.opening om)
        (p.σ (27 + j.val) a) (by omega)
        (flipZ maskPoly B budget P (.opening om) (p.σ (27+j.val) a,b) T' T hd hf)
      have hO : O' = O := Option.some.inj (hview'.symm.trans hview)
      have hom : om' = om := (Msg.opening.inj hm).symm
      subst O'; subst om'
      rw [hσ a] at hc
      rw [Chal.opening.inj hc]
      exact hb
    · exact R0C.V3.DQ.round_field_bound O.statement O.rounds om j.val j.isLt hlen
  · apply one_row_bound maskPoly B budget p (27+j.val) P m T (fun _ => False) _
    · intro a b hf
      obtain ⟨O,om,oc,hview,hm,_,hlen,_⟩ := late_roundBadZ maskPoly B Q m
        (p.σ (27+j.val) a) (by omega)
        (flipZ maskPoly B budget P m (p.σ (27+j.val) a,b) T' T hd hf)
      exact hp ⟨O,om,hview,hm,by omega⟩
    · simp only [indicator_false, mean_const]
      exact R0C.SlackDensity.epsilonSlack_nonneg R0C.ConcreteSlack.delta0_nonneg j.val

#print axioms late_roundBadZ
#print axioms opening_fieldZ_D2
end
end R0P.Mask
