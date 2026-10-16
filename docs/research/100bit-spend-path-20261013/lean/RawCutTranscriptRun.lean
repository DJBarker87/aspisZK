import CanonicalCutEnrichedTranscript
import R1LiteralByteProtocol

/-! The constructed commitment-cut metadata can be installed in the actual
literal byte-protocol run without changing any hash call or challenge.
For a decision on erased bytes, even the complete verifier program is equal.
This does not identify that decision with Rust acceptance or prove decoder
round completion. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutTranscriptRun

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralTranscript CanonicalCutEnrichedTranscript

def proof (w : Words) (pf : AspisR1.LiteralProtocol.Proof) : AspisR1.LiteralProtocol.Proof :=
  fun i => enrichMessage w (pf i)

theorem prefix_ext (w : Words) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (c : LiteralTranscript.Challenge) :
    enrichPrefix w (P.ext m c) = (enrichPrefix w P).ext (enrichMessage w m) c := by
  cases P
  simp [enrichPrefix, enrichRounds, FS.Prefix.ext]

theorem byte_sampler_eq (i : Nat) (w : Words)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    LiteralByteSampler.samp i (enrichPrefix w P) (enrichMessage w m) =
      LiteralByteSampler.samp i P m := by
  unfold LiteralByteSampler.samp
  rw [sampler_enrich_eq]

theorem transcript_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (w : Words) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : AspisR1.LiteralProtocol.Proof) (n : Nat) :
    (AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub (proof w pf) n =
      enrichPrefix w ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub pf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub (proof w pf) n).ext
          (enrichMessage w (pf n))
          (eval H (LiteralByteSampler.samp n
            ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub (proof w pf) n)
            (enrichMessage w (pf n))).toProgram).2 = _
      rw [ih, byte_sampler_eq, ← prefix_ext]
      rfl

theorem chain_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (w : Words) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : AspisR1.LiteralProtocol.Proof) (i : Nat) :
    (AspisR1.LiteralByteProtocol.protocol decoder).chain H pub (proof w pf) i =
      (AspisR1.LiteralByteProtocol.protocol decoder).chain H pub pf i := by
  change LiteralByteSampler.samp i
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub (proof w pf) i)
      (enrichMessage w (pf i)) = _
  rw [transcript_eq, byte_sampler_eq]
  rfl

abbrev ErasedPrefix :=
  UnifiedSampler.Prefix LiteralTranscript.BytesMessage LiteralTranscript.E SelectedTranscriptParams.L
abbrev ErasedMessage := TranscriptView.Message LiteralTranscript.BytesMessage

def decisionOnBytes (d : ErasedPrefix → ErasedMessage → Bool)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) : Bool :=
  d (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)

theorem decision_enrich (d : ErasedPrefix → ErasedMessage → Bool)
    (w : Words) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    decisionOnBytes d (enrichPrefix w P) (enrichMessage w m) = decisionOnBytes d P m := by
  simp only [decisionOnBytes, erasePrefix_enrich, erase_enrichMessage]

theorem verifierFrom_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (w : Words)
    (pf : AspisR1.LiteralProtocol.Proof) (n : Nat) (P : LiteralTranscript.Prefix) :
    FS2.verifierFrom (AspisR1.LiteralByteProtocol.protocol decoder) (decisionOnBytes d)
      (proof w pf) n (enrichPrefix w P) =
    FS2.verifierFrom (AspisR1.LiteralByteProtocol.protocol decoder) (decisionOnBytes d)
      pf n P := by
  induction n generalizing P with
  | zero =>
      change Program.done (decisionOnBytes d (enrichPrefix w P)
        (enrichMessage w (pf 33))) = Program.done (decisionOnBytes d P (pf 33))
      rw [decision_enrich]
  | succ n ih =>
      change bind (LiteralByteSampler.samp (33 - (n+1)) (enrichPrefix w P)
          (enrichMessage w (pf (33 - (n+1))))).toProgram
          (fun c => FS2.verifierFrom (AspisR1.LiteralByteProtocol.protocol decoder)
            (decisionOnBytes d) (proof w pf) n
            ((enrichPrefix w P).ext (enrichMessage w (pf (33 - (n+1)))) c)) =
        bind (LiteralByteSampler.samp (33 - (n+1)) P (pf (33 - (n+1)))).toProgram
          (fun c => FS2.verifierFrom (AspisR1.LiteralByteProtocol.protocol decoder)
            (decisionOnBytes d) pf n (P.ext (pf (33 - (n+1))) c))
      rw [byte_sampler_eq]
      congr 1
      funext c
      rw [← prefix_ext]
      exact ih _

/-- Exact program equality: changing only the recovered word metadata adds
no oracle calls and preserves the byte-based verifier's acceptance. -/
theorem verifier_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (w : Words)
    (pub : LiteralTranscript.Public) (pf : AspisR1.LiteralProtocol.Proof) :
    FS2.verifier (AspisR1.LiteralByteProtocol.protocol decoder) (decisionOnBytes d) pub (proof w pf) =
      FS2.verifier (AspisR1.LiteralByteProtocol.protocol decoder) (decisionOnBytes d) pub pf := by
  exact verifierFrom_eq decoder d w pf 33 (FS.emptyPrefix pub)

#print axioms byte_sampler_eq
#print axioms transcript_eq
#print axioms chain_eq
#print axioms verifierFrom_eq
#print axioms verifier_eq
end AspisR1.RawCutTranscriptRun
end
