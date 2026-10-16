import LiteralTableWordChoice
import R1LiteralByteProtocol

/-! The concrete table-only word choice finds commitment roots in the actual
erased transcript/current message, including messageAt the commitment's own round. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralTableChoiceRun
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment LiteralTableWordChoice

private theorem erased_rounds (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (n : Nat) :
    (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).rounds =
      (List.range n).map (fun i =>
        (LiteralTranscript.erase (pf i),(LiteralByteProtocol.protocol decoder).chal H pub pf i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (LiteralTranscript.erasePrefix
        (((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext (pf n)
          ((LiteralByteProtocol.protocol decoder).chal H pub pf n))).rounds = _
      rw [LiteralTranscript.erasePrefix_ext]
      simp only [FS.Prefix.ext,ih,List.range_succ,List.map_append,List.map_singleton]

theorem at_actual (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n i : Nat) (hi : i ≤ n) :
    messageAt (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
      (LiteralTranscript.erase (pf n)) i = some (LiteralTranscript.erase (pf i)) := by
  have hr : (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).round = n := by
    rw [LiteralTranscript.erasePrefix_round,FS2.transcript_round]
  by_cases he : i = n
  · subst i
    simp [messageAt,hr]
  · rw [at_past _ _ i (by omega),erased_rounds]
    simp [List.getElem?_range,show i < n by omega]

theorem c1_root (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) (r : State) (w : LiteralTranscript.C1Word) (h0 : pf 0 = .initial r w) :
    c1Root (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
      (LiteralTranscript.erase (pf n)) = r := by
  apply c1Root_of_message
  rw [at_actual decoder H pub pf n 0 (by omega),h0]
  rfl

theorem c2_root (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) (hn : 2 ≤ n) (b : LiteralTranscript.BytesMessage)
    (w : LiteralTranscript.C2Word) (r : State) (h2 : pf 2 = .c2 b w)
    (hp : SemanticRecordCodec.decode ⟨2,by decide⟩ b.val = some ⟨.c2Root r,by rfl⟩) :
    c2Root (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
      (LiteralTranscript.erase (pf n)) = r := by
  apply c2Root_of_message _ _ b r _ hp
  rw [at_actual decoder H pub pf n 2 hn,h2]
  rfl

theorem final_root (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) (hn : 30 ≤ n) (b : LiteralTranscript.BytesMessage)
    (w : LiteralTranscript.VWord) (v : OpeningRecordCodec.Payload .second)
    (h30 : pf 30 = .second b w) (hp : OpeningRecordCodec.decode .second b.val = some v) :
    finalRoot (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
      (LiteralTranscript.erase (pf n)) = v.1 := by
  apply finalRoot_of_message _ _ b v _ hp
  rw [at_actual decoder H pub pf n 30 hn,h30]
  rfl

#print axioms at_actual
#print axioms c1_root
#print axioms c2_root
#print axioms final_root
end AspisR1.LiteralTableChoiceRun
end
