import BackgroundCanonicalLabels

/-! Canonical-address support of every successful component of the actual
33-row decoder. No extra validity premise on parsed contexts is required. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedDecoderCanonical
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open BackgroundCanonicalLabels CanonicalByteAddress

variable {M Cv : Type} {L : Nat}

theorem component_good (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hn : n < 33)
    (a : Addr L) (ha : Canonical a) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.component p hD pub n a T = some (own,pend,g)) :
    Good own pend := by
  by_cases h0 : n = 0
  · subst n
    rw [UnifiedDecoder.component_initial] at hd
    apply lifted_good _ a T own pend g hd
    intro s ps out hs
    obtain ⟨c1,hparse,he⟩ := UnifiedInitialDecoder.decode_sound p hD pub a T s ps out hs
    cases he
    exact ⟨initial p hD a ha,by simp⟩
  · by_cases hsem : n < 26
    · rw [UnifiedDecoder.component_semantic p hD pub n (by omega) hsem] at hd
      apply lifted_good _ a T own pend g hd
      intro s ps out hs
      obtain ⟨ctx,hparse,hlo,hhi,he⟩ := UnifiedSemanticDecoder.decode_sound p pub a T s ps out hs
      cases he
      exact ⟨plain p a ha,pend_of_canonical _ (prefix_missing p T ctx.records)⟩
    · by_cases h26 : n = 26
      · subst n
        rw [UnifiedDecoder.component_reseed] at hd
        apply lifted_good _ a T own pend g hd
        intro s ps out hs
        obtain ⟨ctx,hparse,hlen,he⟩ := UnifiedReseedDecoder.decode_sound p pub a T s ps out hs
        cases he
        exact ⟨reseed p pub a ha,pend_of_canonical _ (prefix_missing p T ctx.records)⟩
      · by_cases h31 : n = 31
        · subst n
          rw [UnifiedDecoder.component_query] at hd
          obtain ⟨ctx,hparse,hlen,he⟩ := UnifiedQueryDecoder.decode_sound p pub a T own pend g hd
          cases he
          exact ⟨query p a ha,pend_of_canonical _ (prefix_missing p T ctx.records)⟩
        · by_cases h32 : n = 32
          · subst n
            rw [UnifiedDecoder.component_rho] at hd
            apply lifted_good _ a T own pend g hd
            intro s ps out hs
            obtain ⟨ctx,hparse,hlen,he⟩ := JointUnifiedDecoder.decode_sound p pub 27 4 a T s ps out hs
            cases he
            exact ⟨plain p a ha,pend_of_canonical _
              (joint_missing p T ctx.records ctx.endpoint)⟩
          · rw [UnifiedDecoder.component_opening p hD pub n (by omega) (by omega)] at hd
            apply lifted_good _ a T own pend g hd
            intro s ps out hs
            obtain ⟨ctx,hparse,hlo,hhi,he⟩ := UnifiedOpeningDecoder.decode_sound p pub a T s ps out hs
            cases he
            exact ⟨plain p a ha,pend_of_canonical _ (prefix_missing p T ctx.records)⟩

theorem decode_good (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (ha : Canonical a)
    (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.decode p hD pub a T = some (own,pend,g)) :
    Good own pend := by
  obtain ⟨n,hn,hcomp⟩ := UnifiedDecoder.decode_sound p hD pub a T own pend g hd
  exact component_good p hD pub n hn a ha T own pend g hcomp

#print axioms component_good
#print axioms decode_good
end AspisR1.UnifiedDecoderCanonical
end
