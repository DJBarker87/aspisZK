import LiteralDecoderEnrichment
import RawByteTableWords
import R1OpeningRecordCodec
import R1SemanticRecordCodec

/-! Concrete decoder word selection. It reads only the supplied current table
and roots in the decoded prefix/current message, never the current challenge
or a future trace. Malformed/missing roots have a fixed zero default. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralTableWordChoice
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

def messageAt (P : ErasedPrefix) (m : ErasedMessage) (i : Nat) : Option ErasedMessage :=
  if P.round = i then some m else (P.rounds[i]?).map Prod.fst

def c1Root (P : ErasedPrefix) (m : ErasedMessage) : State :=
  ((messageAt P m 0).bind fun msg => match msg with
    | .initial r => some r
    | _ => none).getD default

def c2Root (P : ErasedPrefix) (m : ErasedMessage) : State :=
  ((messageAt P m 2).bind fun msg => match msg with
    | .payload b => (SemanticRecordCodec.decode ⟨2,by decide⟩ b.val).bind fun parsed =>
        match parsed.val with | .c2Root r => some r | _ => none
    | _ => none).getD default

def finalRoot (P : ErasedPrefix) (m : ErasedMessage) : State :=
  ((messageAt P m 30).bind fun msg => match msg with
    | .payload b => (OpeningRecordCodec.decode .second b.val).map Prod.fst
    | _ => none).getD default

def choose (_ : Bytes) (T : Table Bytes State) (P : ErasedPrefix) (m : ErasedMessage) : Words :=
  RawByteTableWords.words T T T (c1Root P m) (c2Root P m) (finalRoot P m)

theorem at_current (P : ErasedPrefix) (m : ErasedMessage) : messageAt P m P.round = some m := by
  simp [messageAt]

theorem at_past (P : ErasedPrefix) (m : ErasedMessage) (i : Nat) (hi : i < P.round) :
    messageAt P m i = (P.rounds[i]?).map Prod.fst := by simp [messageAt,show P.round ≠ i by omega]

theorem c1Root_of_message (P : ErasedPrefix) (m : ErasedMessage) (r : State)
    (h : messageAt P m 0 = some (.initial r)) : c1Root P m = r := by simp [c1Root,h]

theorem c2Root_of_message (P : ErasedPrefix) (m : ErasedMessage)
    (b : LiteralTranscript.BytesMessage) (r : State)
    (h : messageAt P m 2 = some (.payload b))
    (hp : SemanticRecordCodec.decode ⟨2,by decide⟩ b.val = some ⟨.c2Root r,by rfl⟩) :
    c2Root P m = r := by
  unfold c2Root
  rw [h]
  change ((SemanticRecordCodec.decode ⟨2,by decide⟩ b.val).bind fun parsed =>
    match parsed.val with | .c2Root r => some r | _ => none).getD default = r
  rw [hp]
  rfl

theorem finalRoot_of_message (P : ErasedPrefix) (m : ErasedMessage)
    (b : LiteralTranscript.BytesMessage) (payload : OpeningRecordCodec.Payload .second)
    (h : messageAt P m 30 = some (.payload b))
    (hp : OpeningRecordCodec.decode .second b.val = some payload) :
    finalRoot P m = payload.1 := by
  unfold finalRoot
  rw [h]
  change ((OpeningRecordCodec.decode .second b.val).map Prod.fst).getD default = payload.1
  rw [hp]
  rfl

#print axioms c1Root_of_message
#print axioms c2Root_of_message
#print axioms finalRoot_of_message
end AspisR1.LiteralTableWordChoice
end
