import LiteralDecoderEnrichment
import RawCutTranscriptRun

/-! Reconstruct the literal metadata of an actual transcript from its erased
restorePrefix. Only messages already present in the restorePrefix must agree. Future
commitment words are not constrained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralDecoderPrefixRestore
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

theorem rounds_append (w : Words) (i : Nat)
    (rs tail : List (ErasedMessage × LiteralTranscript.Challenge)) :
    rounds w i (rs ++ tail) = rounds w i rs ++ rounds w (i+rs.length) tail := by
  induction rs generalizing i with
  | nil => simp [rounds]
  | cons q rest ih => simp [rounds,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem prefix_ext (w : Words) (P : ErasedPrefix) (m : ErasedMessage)
    (c : LiteralTranscript.Challenge) :
    restorePrefix w (P.ext m c) = (restorePrefix w P).ext (message w P.round m) c := by
  cases P with
  | mk pub rs => simp [restorePrefix,FS.Prefix.ext,rounds_append,rounds,FS.Prefix.round]

theorem actual_prefix (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (w W : Words) (n : Nat)
    (hvalid : ∀ i < n, LiteralTranscript.valid i (pf i))
    (hwords : ∀ i < n, enrichMessage w (pf i) = enrichMessage W (pf i)) :
    restorePrefix w (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)) =
      enrichPrefix W ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change restorePrefix w (LiteralTranscript.erasePrefix
        (((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext (pf n)
          ((LiteralByteProtocol.protocol decoder).chal H pub pf n))) = _
      rw [LiteralTranscript.erasePrefix_ext,prefix_ext]
      rw [ih (fun i hi => hvalid i (by omega)) (fun i hi => hwords i (by omega))]
      have hr : (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).round = n := by
        rw [LiteralTranscript.erasePrefix_round,FS2.transcript_round]
      rw [hr,message_of_valid w n (pf n) (hvalid n (by omega)),hwords n (by omega)]
      exact (RawCutTranscriptRun.prefix_ext W
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n)
        ((LiteralByteProtocol.protocol decoder).chal H pub pf n)).symm

#print axioms prefix_ext
#print axioms actual_prefix
end AspisR1.LiteralDecoderPrefixRestore
end
