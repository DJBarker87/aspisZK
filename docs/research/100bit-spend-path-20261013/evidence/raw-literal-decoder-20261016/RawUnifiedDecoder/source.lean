import UnifiedDecoderCanonical
import RawBackgroundCompletion
import R1UnifiedDecoderBound

/-! Concrete raw-byte decoder obtained from the checked existing 33-row
unified decoder. Only canonical verifier addresses are decoded; adversarial
oracle queries remain unrestricted. Follow and law are preserved exactly. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawUnifiedDecoder
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.OracleResampling
open CanonicalAddressEmbedding
variable {M Cv : Type} {L : Nat}

abbrev Completion (M Cv : Type) (L : Nat) :=
  BS Bytes State (List State) × List (Bytes × Option State) ×
    (List State → List State → JointTranscriptView.Output M Cv L)

def atCanonical (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : AddrC L) (T : Table Bytes State) :
    Option (Completion M Cv L) :=
  match hd : UnifiedDecoder.decode p hD pub a.val (RawBoundedTrace.table L T) with
  | none => none
  | some (s,ps,g) =>
      let hg := UnifiedDecoderCanonical.decode_good p hD pub a.val a.property
        (RawBoundedTrace.table L T) s ps g hd
      some (RawBackgroundCompletion.own s hg.1,RawBackgroundCompletion.pending ps hg.2,g)

def decode (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L) :
    Dec (UnifiedSampler.Public L) (TranscriptView.Message M) (TranscriptView.Challenge Cv)
      Bytes State (List State) :=
  fun a T => (CanonicalRawTrace.decode L a).bind (fun a => atCanonical p hD pub a T)

theorem atCanonical_of_decode (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : AddrC L) (T : Table Bytes State)
    (s : BS (Addr L) State (List State)) (ps : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.decode p hD pub a.val (RawBoundedTrace.table L T) = some (s,ps,g)) :
    let hg := UnifiedDecoderCanonical.decode_good p hD pub a.val a.property
      (RawBoundedTrace.table L T) s ps g hd
    atCanonical p hD pub a T =
      some (RawBackgroundCompletion.own s hg.1,RawBackgroundCompletion.pending ps hg.2,g) := by
  dsimp only
  unfold atCanonical
  split
  · rename_i hn
    rw [hd] at hn
    cases hn
  · rename_i bs bp bg he
    have heq := Option.some.inj (he.symm.trans hd)
    cases heq
    rfl

theorem atCanonical_none (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : AddrC L) (T : Table Bytes State)
    (hd : UnifiedDecoder.decode p hD pub a.val (RawBoundedTrace.table L T) = none) :
    atCanonical p hD pub a T = none := by
  unfold atCanonical
  split
  · rfl
  · rename_i bs bp bg he
    rw [hd] at he
    cases he

theorem decode_of_canonical (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : AddrC L) (T : Table Bytes State) :
    decode p hD pub (toBytes a) T = atCanonical p hD pub a T := by
  have hd := (CanonicalRawTrace.embedding L).decode_embed a
  change CanonicalRawTrace.decode L (toBytes a) = some a at hd
  simp [decode,hd]

theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Bytes) (T : Table Bytes State)
    (s : BS Bytes State (List State)) (ps : List (Bytes × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p hD pub a T = some (s,ps,g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : TranscriptView.Message M),
      i < 33 → P.rounds.length = i →
        AspisV8R19.AdaptiveFirstReadLaw.independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P,m,w.2)) ≤ B) : blaw g obs s ps ≤ B := by
  unfold decode at hd
  cases ha : CanonicalRawTrace.decode L a with
  | none => simp [ha] at hd
  | some ac =>
      simp only [ha,Option.bind_some] at hd
      cases hc : UnifiedDecoder.decode p hD pub ac.val (RawBoundedTrace.table L T) with
      | none => rw [atCanonical_none p hD pub ac T hc] at hd; cases hd
      | some result =>
          rcases result with ⟨bs,bp,bg⟩
          rw [atCanonical_of_decode p hD pub ac T bs bp bg hc] at hd
          have hb := UnifiedDecoderBound.decoded_bound p hD pub ac.val
            (RawBoundedTrace.table L T) bs bp bg hc obs B hfixed
          cases hd
          rw [RawBackgroundCompletion.blaw_eq]
          exact hb

theorem decodes_and_follows_of_legacy (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : AddrC L) (T : Table Bytes State)
    (tr : List (Bytes × State)) (out : JointTranscriptView.Output M Cv L)
    (hlegacy : ∃ bs bp bg,
      UnifiedDecoder.decode p hD pub a.val (RawBoundedTrace.table L T) = some (bs,bp,bg) ∧
        bfollow bg (RawBoundedTrace.trace L tr) bs bp (RawBoundedTrace.table L T) = some out) :
    ∃ s ps g, decode p hD pub (toBytes a) T = some (s,ps,g) ∧
      bfollow g tr s ps T = some out := by
  obtain ⟨bs,bp,bg,hd,hf⟩ := hlegacy
  let hg := UnifiedDecoderCanonical.decode_good p hD pub a.val a.property
    (RawBoundedTrace.table L T) bs bp bg hd
  refine ⟨RawBackgroundCompletion.own bs hg.1,RawBackgroundCompletion.pending bp hg.2,bg,?_,?_⟩
  · rw [decode_of_canonical]
    exact atCanonical_of_decode p hD pub a T bs bp bg hd
  · rw [RawBackgroundCompletion.bfollow_eq]
    exact hf

#print axioms decoded_bound
#print axioms decodes_and_follows_of_legacy
end AspisR1.RawUnifiedDecoder
end
