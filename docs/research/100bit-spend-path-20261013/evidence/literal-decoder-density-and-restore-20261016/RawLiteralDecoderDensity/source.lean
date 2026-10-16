import RawUnifiedDecoder
import LiteralDecoderEnrichment
import R1BackgroundLawMap
import R1LiteralByteProtocol

/-! All-33-round background-decoder density for the literal no-hit classifier.
The commitment words are chosen from the decoder's input table, erased restorePrefix,
and current message, before the current challenge. Concrete word recovery and
successful-run enrichment are separate deterministic obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawLiteralDecoderDensity
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript
abbrev Output := ErasedPrefix × ErasedMessage × LiteralTranscript.Challenge
abbrev LiteralOutput := LiteralTranscript.Prefix × LiteralTranscript.Message × LiteralTranscript.Challenge
abbrev WordChoice := Bytes → Table Bytes State → ErasedPrefix → ErasedMessage → Words

def restore (choose : ErasedPrefix → ErasedMessage → Words) (out : Output) : LiteralOutput :=
  let w := choose out.1 out.2.1
  (restorePrefix w out.1,message w out.1.round out.2.1,out.2.2)

def decode (choose : WordChoice) (pub : LiteralTranscript.Public) :
    Dec LiteralTranscript.Public LiteralTranscript.Message LiteralTranscript.Challenge
      Bytes State (List State) :=
  fun a T => (RawUnifiedDecoder.decode SelectedTranscriptParams.params
    (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T).map
      (fun (s,ps,g) => (s,ps,fun x as => restore (choose a T) (g x as)))

theorem density (protocolDecoder : LiteralByteProtocol.Decoder) (choose : WordChoice)
    (pub : LiteralTranscript.Public) :
    ChainDensity3 (LiteralByteProtocol.protocol protocolDecoder) LiteralByteProtocol.rows
      (decode choose pub) := by
  intro a T s ps g hd
  unfold decode at hd
  cases hc : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T with
  | none => simp [hc] at hd
  | some result =>
      rcases result with ⟨bs,bp,bg⟩
      simp only [hc,Option.map_some] at hd
      have hbound : blaw bg
          (fun out => indicator (FS2.d2Bad (LiteralByteProtocol.protocol protocolDecoder)
            LiteralByteProtocol.rows (restore (choose a T) out).1
            (restore (choose a T) out).2.1 T (restore (choose a T) out).2.2)) bs bp ≤
          FS.maxErr LiteralClassifier.budget 33 := by
        refine RawUnifiedDecoder.decoded_bound SelectedTranscriptParams.params
          (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
          pub a T bs bp bg hc _ (FS.maxErr LiteralClassifier.budget 33) ?_
        intro i P m hi hround
        have hr : P.round = i := hround
        subst i
        let w := choose a T P m
        apply le_trans _ ((LiteralDecoderEnrichment.density w P m hi).trans
          (FS.le_maxErr LiteralClassifier.budget 33 P.round hi))
        apply GenericNoHitFS2.independentMean_mono
        intro v
        apply indicator_mono
        intro hbad
        obtain ⟨_,⟨T',hdoomed⟩,hnot⟩ := hbad
        exact GenericNoHit.doomed_ext_bad LiteralClassifier.bad LiteralProtocol.relation
          (restorePrefix w P) (message w P.round m) v.2 hdoomed hnot
      cases hd
      rw [BackgroundLawMap.blaw_map]
      exact hbound

#print axioms density
end AspisR1.RawLiteralDecoderDensity
end
