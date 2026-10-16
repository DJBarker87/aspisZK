import LiteralDecoderPrefixRestore

/-! Only words committed by the current round are needed to restore its
prefix and message. Later commitment metadata is unconstrained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralWordAgreement
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

theorem message_eq (w W : Words) (n i : Nat) (m : LiteralTranscript.Message)
    (hi : i ≤ n) (hvalid : LiteralTranscript.valid i m)
    (h1 : w.c1 = W.c1) (h2 : 2 ≤ n → w.c2 = W.c2)
    (h30 : 30 ≤ n → w.final = W.final) :
    enrichMessage w m = enrichMessage W m := by
  cases m with
  | initial root word =>
      change LiteralTranscript.Message.initial root w.c1 = .initial root W.c1
      rw [h1]
  | payload b => rfl
  | c2 b word =>
      have he : i = 2 := by
        unfold LiteralTranscript.valid at hvalid
        split at hvalid <;> simp_all
      change LiteralTranscript.Message.c2 b w.c2 = .c2 b W.c2
      rw [h2 (by omega)]
  | second b word =>
      have he : i = 30 := by
        unfold LiteralTranscript.valid at hvalid
        split at hvalid <;> simp_all
      change LiteralTranscript.Message.second b w.final = .second b W.final
      rw [h30 (by omega)]

theorem actual_output (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (w W : Words) (n : Nat)
    (hvalid : ∀ i ≤ n, LiteralTranscript.valid i (pf i))
    (h1 : w.c1 = W.c1) (h2 : 2 ≤ n → w.c2 = W.c2)
    (h30 : 30 ≤ n → w.final = W.final) :
    (restorePrefix w (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)),
      message w n (LiteralTranscript.erase (pf n)),
      (LiteralByteProtocol.protocol decoder).chal H pub pf n) =
    (enrichPrefix W ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
      enrichMessage W (pf n),(LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  have hp := LiteralDecoderPrefixRestore.actual_prefix decoder H pub pf w W n
    (fun i hi => hvalid i (by omega))
    (fun i hi => message_eq w W n i (pf i) (by omega) (hvalid i (by omega)) h1 h2 h30)
  have hm := (message_of_valid w n (pf n) (hvalid n (by omega))).trans
    (message_eq w W n n (pf n) (by omega) (hvalid n (by omega)) h1 h2 h30)
  rw [hp,hm]

#print axioms message_eq
#print axioms actual_output
end AspisR1.LiteralWordAgreement
end
